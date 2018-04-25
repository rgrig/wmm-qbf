(* This is likely only to work on POSIX. *)

(* Thrown when the called subprocess encounters an error. *)
(* Gives a short reason, and stderr from the process. *)
exception SubprocessFailed of string * string

(* Read from a file descriptor into a buffer, ignoring irrelevant blocking errors. *)
(* Return true on EOF. *)
let nonblock_read file buffer =
  try
    let max_bytes = 256 in
    let chunk = Bytes.create max_bytes in
    let bytes_read = Unix.read file chunk 0 max_bytes in
    Buffer.add_subbytes buffer chunk 0 bytes_read;
    bytes_read = 0
  (* NOTE: EWOULDBLOCK is only for sockets according to read(3) *)
  (* NOTE: EAGAIN only occurs if no bytes are read. *)
  with Unix.Unix_error (Unix.EAGAIN, _, _) -> false

(* Write from a buffer to a file descriptor, ignoring irrelevant blocking errors. *)
let nonblock_write buffer offset file =
  try
    let remaining = (Bytes.length buffer) - !offset in
    if remaining <> 0 then begin
      let bytes_written = Unix.single_write file buffer !offset remaining in
      offset := !offset + bytes_written;

      if !offset = Bytes.length buffer then begin
        Unix.close file;
      end
    end
  (* NOTE: EWOULDBLOCK is only for sockets according to write(3) *)
  (* NOTE: EAGAIN only occurs if no bytes are written. *)
  with Unix.Unix_error (Unix.EAGAIN, _, _) -> ()

(* This seems elegant to me, perhaps people with better tastes would
   disagree though - sjc*)
let program_in_path p =
  (Sys.command ("which " ^ p ^ "> /dev/null")) = 0

let run_program program options data =
  if not (program_in_path program) then
    raise (SubprocessFailed ("missing executable (" ^ program ^ ")", ""));

  if (Config.verbose ()) then (
    Printf.eprintf "running `%s'\n" (String.concat " " (program :: (Array.to_list options)));
    flush stderr;
  );

  (* Create stdio pipes to talk to subprocess. *)
  (* NOTE: Pipes could be left open if an exception is thrown, doesn't matter if we're only called once. *)
  let (child_stdin_r, child_stdin_w) = Unix.pipe () in
  let (child_stdout_r, child_stdout_w) = Unix.pipe () in
  let (child_stderr_r, child_stderr_w) = Unix.pipe () in

  (* Mark our end of each pipe to be closed by the child. *)
  List.iter (Unix.set_close_on_exec) [child_stdin_w; child_stdout_r; child_stderr_r];

  (* Launch process with the new pipes. *)
  (* NOTE: Using create_process to avoid calling /bin/sh because it might cause trouble. *)
  let pid = Unix.create_process program
      (Array.append [|program|] options)
      child_stdin_r child_stdout_w child_stderr_w
  in

  (* Ignore SIGPIPE. *)
  (* NOTE: This happens after forking the subprocess, so the
     subprocess will still terminate if its stdout *)
  (* is closed (if the parent process - this process - dies, etc). *)
  let old_sigpipe = Sys.signal Sys.sigpipe Sys.Signal_ignore in

  (* Close our copy of child's end of each pipe. *)
  List.iter Unix.close [child_stdin_r; child_stdout_w; child_stderr_w];

  (* Make pipes nonblocking so we can check each in turn. *)
  List.iter Unix.set_nonblock [child_stdin_w; child_stdout_r; child_stderr_r];

  (* Setup buffers for IO. *)
  let to_child_offset = ref 0 in
  let to_child_data = Bytes.of_string data in
  let output = Buffer.create 16 in
  let errors = Buffer.create 16 in

  (* Concurrently write stdin, read stdout, read stderr, until subprocess ends and closes stdout. *)
  (* Works this way because a blocking write of all input could block waiting for the process to read. *)
  (* The process won't read if it's own output pipe is blocked, which it might be if we don't read it. *)
  (* On Linux the default pipe buffer is ~64KB but typical solver input (if I remember rightly) was *)
  (* in the hundreds of KB. *)
  (* TODO: Avoid polling (ideally). *)
  let waiting = ref true in
  (* If you're a functional purist, how much do you hate me right now? :P *)
  begin try
      while !waiting do
        (* Poll each pipe, doing this with select() would be very awkward. *)
        nonblock_write to_child_data to_child_offset child_stdin_w;
        if nonblock_read child_stdout_r output &&
           nonblock_read child_stderr_r output
        then waiting := false;

        (* Let the OS do something else. *)
        Unix.sleepf 0.01;
      done
    (* Ignore broken pipe because it means the process exited before reading all it's input. *)
    (* In that case we want to continue so we can find out what happened. *)
    with Unix.Unix_error (Unix.EPIPE, _, _) -> ()
  end;

  (* Close pipes. *)
  Unix.close child_stdout_r;
  Unix.close child_stderr_r;

  (* Re-enable SIGPIPE. *)
  ignore (Sys.signal Sys.sigpipe old_sigpipe);

  (* Clean up zombie subprocess and get it's exit code. *)
  let (_, status) = Unix.waitpid [] pid in
  match status with
  (* Success. *)
  (* TODO: Interpret status code. *)
  (* Non-zero is normally an error, but the solver returns code 10 for what looks like a non-error case. *)
  | Unix.WEXITED _ -> Buffer.contents output
  | Unix.WSIGNALED status ->
    raise (SubprocessFailed (
        (Printf.sprintf "Caught signal %d" status),
        (Buffer.contents errors)
      ))
  | Unix.WSTOPPED status -> raise (SubprocessFailed (
      (Printf.sprintf "Stopped by signal %d" status),
      (Buffer.contents errors)
    ))

let run_qbf_solver options data =
  run_program (Config.qbf_solver_bin ()) options data
let run_so_solver options data =
  run_program (Config.so_solver_bin ()) options data
