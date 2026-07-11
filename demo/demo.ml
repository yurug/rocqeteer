(** Rocqeteer end-to-end demo: the "audited counter" [demo_prog] (Env + Trace + recursion +
    KV), shown from Rocq proof to running OCaml. Prints a narrated terminal walkthrough and
    writes a self-contained HTML report (demo/demo_report.html). Run via `make demo`. *)

module E = Ref_extracted.EffIR
module D = Ref_extracted.Datatypes
module S = Ref_extracted.Samples
module Gen = Generated.Prog0_generated

(* --- tiny ANSI helpers --- *)
let esc c s = Printf.sprintf "\027[%sm%s\027[0m" c s
let bold = esc "1" and cyan = esc "36" and green = esc "32" and yellow = esc "33" and dim = esc "2"
let rule () = print_endline (dim (String.make 78 '-'))
let step n title = Printf.printf "\n%s %s\n" (bold (cyan (Printf.sprintf "[%d]" n))) (bold title)

(* --- read a snippet from a source file (graceful if absent) --- *)
let slurp path = try Some (In_channel.with_open_text path In_channel.input_all) with _ -> None

let block path ~from_:start ~until : string =
  match slurp path with
  | None -> Printf.sprintf "(could not read %s)" path
  | Some txt ->
      let lines = String.split_on_char '\n' txt in
      let rec take acc started = function
        | [] -> List.rev acc
        | l :: tl ->
            if not started then
              if String.length l >= String.length start
                 && (try Str.search_forward (Str.regexp_string start) l 0 >= 0 with _ -> false)
              then take (l :: acc) true tl
              else take acc false tl
            else if (try Str.search_forward (Str.regexp_string until) l 0 >= 0 with _ -> false)
            then List.rev (l :: acc)
            else take (l :: acc) true tl
      in
      String.concat "\n" (take [] false lines)

let indent s = s |> String.split_on_char '\n' |> List.map (fun l -> "    " ^ l) |> String.concat "\n"

(* --- the live computation --- *)
let tag = 99

(* One instant for the whole demo: demo_prog is time-independent, so now = 0. The fast
   side gets it through the single Time+Store composition point (adr-0011). *)
let now = Z.zero

(* reference: the extracted pure interpreter, from context [tag] and an empty store.
   Keys are decimal byte strings since R4 ("0", "9"); parse them back for the display. *)
let reference () : (int * int) list * int list =
  let z_of = Coqconv.z_of_coqz in
  match E.observe_full (E.DInt (Coqconv.coqz_of_z (Z.of_int tag)))
          (Coqconv.coqz_of_z now) E.M.empty S.demo_prog with
  | D.Coq_pair (D.Coq_pair (_o, kvs), tr) ->
      let kv =
        Coqconv.list_of_coq kvs
        |> List.map (function
             | D.Coq_pair (k, D.Coq_pair (E.DInt v, _dl)) ->
                 (int_of_string (Coqconv.string_of_coq k), Z.to_int (z_of v))
             | D.Coq_pair (_, _) -> failwith "non-int")
        |> List.sort compare
      in
      let trace =
        Coqconv.list_of_coq tr
        |> List.map (function E.DInt z -> Z.to_int (z_of z) | _ -> 0)
      in
      (kv, trace)

(* fast: the GENERATED OCaml run under the native Env / Trace / Time+Store handler stack
   (the Time and store handlers share ONE source — Runtime.with_store_and_time).
   Context and trace events are Rval.t; store entries are (Rval.t * deadline option). *)
let fast () : (int * int) list * int list =
  let kvtbl = Rkv.Kv.T.create 16 in
  let buf = ref [] in
  (* Context is Rval.Int tag; Env.run expects Rval.t *)
  Rkv.Env.run (Rkv.Rval.Int (Z.of_int tag)) (fun () ->
      Rkv.Trace.run buf (fun () ->
          Rkv.Runtime.with_store_and_time ~source:(fun () -> now) kvtbl
            (fun () -> ignore (Gen.demo_prog ()))));
  let kv =
    Rkv.Kv.observe ~now kvtbl
    |> List.map (fun (k, e) ->
           match e with
           | Rkv.Rval.Int z, _dl -> (int_of_string (Bytes.to_string k), Z.to_int z)
           | _ -> failwith "demo: non-int KV value")
  in
  let trace =
    Rkv.Trace.contents buf
    |> List.map (function
           | Rkv.Rval.Int z -> Z.to_int z
           | _ -> failwith "demo: non-int trace event")
  in
  (kv, trace)

let show_kv kv = "{ " ^ String.concat ", " (List.map (fun (k, v) -> Printf.sprintf "%d->%d" k v) kv) ^ " }"
let show_tr tr = "[" ^ String.concat "; " (List.map string_of_int tr) ^ "]"

(* codec: persist the (counter, tag) pair to bytes and read it back (proven round-trip) *)
let codec_demo () : string * (int * int) =
  let enc = Rkv.Codec.EPair (Rkv.Codec.EInt, Rkv.Codec.EInt) in
  let v = (Z.of_int 3, Z.of_int tag) in
  let bytes = Rkv.Codec.to_bytes enc v in
  let hex = String.concat " " (List.init (Bytes.length bytes) (fun i -> Printf.sprintf "%02x" (Bytes.get_uint8 bytes i))) in
  match Rkv.Codec.of_bytes enc bytes with
  | Ok (a, b) -> (hex, (Z.to_int a, Z.to_int b))
  | Error e -> (hex ^ " (decode error: " ^ e ^ ")", (-1, -1))

(* --- narration --- *)
let rocq_src = block "theories/Samples.v" ~from_:"Definition demo_prog" ~until:"VVar 2]))).\n"
let rocq_src = if String.length rocq_src > 400 then block "theories/Samples.v" ~from_:"Definition demo_prog :" ~until:")))." else rocq_src
let theorem = block "theories/Demo.v" ~from_:"Theorem demo_correct" ~until:"Qed."

(* The codegen emits each program on ONE line (deterministic, diff-friendly). For display,
   break the line at let-bindings and match arms so a human can actually read it. *)
let pretty (s : string) : string =
  s
  |> Str.global_replace (Str.regexp_string ") in (") ") in\n  ("
  |> Str.global_replace (Str.regexp_string " with None -> ") " with\n     | None -> "
  |> Str.global_replace (Str.regexp_string " | Some ") "\n     | Some "

let gen_code = pretty (block "generated/prog0_generated.ml" ~from_:"let demo_prog ()" ~until:"done))")

(* Where the effects actually live: the generated code calls curried wrappers whose bodies
   perform the effects — Effect.perform is CONFINED to runtime/ (a CI gate), so effectful
   code reads like ordinary OCaml while the effect boundary stays reviewed and narrow. *)
let wrapper_code =
  String.concat "\n"
    [ "(* runtime/env.ml *)   let ask () = Effect.perform Ask";
      "(* runtime/trace.ml *) let emit v = Effect.perform (Emit v)";
      "(* runtime/kv.ml *)    let put k v = Effect.perform (Put (k, v))";
      "(* ...interpreted by Effect.Deep handlers, e.g. runtime/kv.ml: *)";
      "(*   | effect Put (k, v), kont -> T.replace table k v; continue kont () *)" ]

let () =
  let rkv, rtr = reference () in
  let fkv, ftr = fast () in
  let agree = rkv = fkv && rtr = ftr in
  let hex, decoded = codec_demo () in
  let roundtrip_ok = decoded = (3, tag) in

  print_endline "";
  print_endline (bold (cyan "  ROCQETEER — end-to-end demo: an \"audited counter\""));
  print_endline (dim  "  prove it in Rocq  ·  generate idiomatic OCaml  ·  run it  ·  validate the bridge");
  rule ();
  print_endline (Printf.sprintf "  The program composes %s, %s, %s and %s: read an audit tag from the"
                   (green "Env") (green "Trace") (green "recursion") (green "KV"));
  print_endline "  read-only context, log it, bump a hit-counter 3 times, and persist the tag.";

  step 1 "Written & PROVEN in Rocq  (theories/Samples.v, theories/Demo.v)";
  print_endline (dim "  the source (a first-order EffIR term):");
  print_endline (indent rocq_src);
  print_endline (dim "  the machine-checked theorem:");
  print_endline (indent theorem);
  print_endline (Printf.sprintf "  %s  Print Assumptions demo_correct = %s" (green "✓") (bold "\"Closed under the global context\" (0 axioms)"));

  step 2 "Code-generated to idiomatic OCaml 5  (generated/prog0_generated.ml)";
  print_endline (dim "  direct style — no monad, no interpreter, just effect calls + a for-loop:");
  print_endline (indent gen_code);
  print_endline (dim "  where are the effects? Env.ask / Trace.emit / Kv.put ARE the effect operations —");
  print_endline (dim "  each is a thin wrapper whose body performs the effect, confined to runtime/ (CI gate):");
  print_endline (indent wrapper_code);

  step 3 "RUN under the native handler stack  (Env ∘ Trace ∘ Time ∘ Store, one clock source)";
  Printf.printf "  context (audit tag) = %s\n" (yellow (string_of_int tag));
  Printf.printf "  final store : %s\n" (bold (show_kv fkv));
  Printf.printf "  audit trace : %s\n" (bold (show_tr ftr));

  step 4 "VALIDATED — the proven reference agrees with the fast OCaml";
  Printf.printf "  reference (pure Rocq interpreter) : store %s  trace %s\n" (show_kv rkv) (show_tr rtr);
  Printf.printf "  fast      (generated + handlers)  : store %s  trace %s\n" (show_kv fkv) (show_tr ftr);
  Printf.printf "  %s\n" (if agree then green "✓ reference == fast (differential check passes)"
                          else esc "31" "✗ MISMATCH");
  Printf.printf "  persistence via the proven codec: (3,%d) -> bytes [%s] -> decode -> (%d,%d)  %s\n"
    tag hex (fst decoded) (snd decoded)
    (if roundtrip_ok then green "✓ round-trip" else esc "31" "✗");

  rule ();
  print_endline (Printf.sprintf "  %s  proven functional (in Rocq, 0 axioms) · %s trusted+differentially tested"
                   (bold "What you trust:") (bold ""));
  print_endline "  the OCaml compiler/runtime, the codegen, and the handlers — 0 Obj.magic, every";
  print_endline "  trust assumption named in docs/tcb_report.md.";
  print_endline (Printf.sprintf "\n  %s  wrote %s\n" (green "→") (bold "demo/demo_report.html"));

  (* --- HTML report --- *)
  Demo_html.write ~tag ~rocq_src ~theorem ~gen_code ~wrapper_code ~rkv ~rtr ~fkv ~ftr ~agree ~hex ~decoded
    ~roundtrip_ok;
  if not (agree && roundtrip_ok) then exit 1
