open Printf

module E = EventStructure
module U = Util

let enums = [
  ("j+r", JR.do_enum)
  (* ; ("pes", PES.do_enum) *)
]

let decides = [
  ("j+r", JR.do_decide)
; ("pes", PES.do_decide)
]


let enum_mode = ref false
let default_model = List.hd decides
let model_name = ref (fst default_model)

let pick_model m models =
  let rec p ms =
    match ms with
      (x, f)::ms when x = m -> f
    | _::ms -> p ms
    | [] ->
      eprintf "Could not find model `%s'. Executing with model `%s' instead.\n" m (fst (List.hd models));
      snd (List.hd models)
  in
  p models

let do_one fn =
  let es, target = U.parse fn in
  let fn = Filename.remove_extension fn in
  if !enum_mode
  then (pick_model !model_name enums) fn es target
  else (match target with
    | None -> eprintf "W: skipping %s: no target execution\n" fn
    | Some target -> (pick_model !model_name decides) fn es target
    )

let cmd_spec =
  Arg.align [
    "-e", Arg.Set enum_mode, "  enumerate all executions"
  ;"--model", Arg.Set_string model_name, (Format.sprintf "  pick a model. Default is %s" !model_name)
  ]

let () =
  Arg.parse cmd_spec do_one (sprintf "%s <infiles>" (Sys.executable_name))
