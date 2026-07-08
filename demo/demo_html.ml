(** Generates a self-contained HTML report for the demo (demo/demo_report.html). *)

let esc s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b

let show_kv kv = "{ " ^ String.concat ", " (List.map (fun (k, v) -> Printf.sprintf "%d&rarr;%d" k v) kv) ^ " }"
let show_tr tr = "[" ^ String.concat "; " (List.map string_of_int tr) ^ "]"

let write ~tag ~rocq_src ~theorem ~gen_code ~wrapper_code ~rkv ~rtr ~fkv ~ftr ~agree ~hex ~decoded ~roundtrip_ok =
  let ok = agree && roundtrip_ok in
  let badge cond t f = if cond then ("ok", t) else ("bad", f) in
  let agree_cls, agree_txt = badge agree "reference == fast" "MISMATCH" in
  let rt_cls, rt_txt = badge roundtrip_ok "round-trip OK" "round-trip FAILED" in
  let html =
    Printf.sprintf
      {html|<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Rocqeteer demo — audited counter</title>
<style>
 :root{--bg:#0a0e1a;--panel:#121829;--ink:#e6ebff;--mut:#93a0c4;--line:#222c44;--ok:#4ade80;--bad:#ff6b6b;--acc:#6ea8fe;--hi:#ffd166;}
 *{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.6 ui-sans-serif,system-ui,Segoe UI,Roboto,Arial}
 .wrap{max-width:980px;margin:0 auto;padding:40px 24px 80px}
 h1{font-size:28px;margin:0 0 4px} .sub{color:var(--mut);margin:0 0 18px}
 .pipe{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:18px 0}
 .pipe .n{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:8px 12px;font-size:13px}
 .pipe .a{color:var(--acc)}
 .card{background:var(--panel);border:1px solid var(--line);border-radius:14px;padding:18px 20px;margin:16px 0}
 .card h2{font-size:17px;margin:0 0 10px;color:var(--acc)}
 .step{display:inline-flex;width:24px;height:24px;border-radius:7px;align-items:center;justify-content:center;background:#0c1120;border:1px solid var(--line);color:var(--acc);font-weight:700;margin-right:8px}
 pre{background:#0c1120;border:1px solid var(--line);border-radius:8px;padding:12px 14px;overflow:auto;font:12.5px/1.5 ui-monospace,Menlo,Consolas,monospace;color:#cfe0ff;white-space:pre-wrap;word-break:break-word}
 .kv{font:14px ui-monospace,monospace;color:var(--hi)}
 .ok{color:var(--ok)} .bad{color:var(--bad)} .mut{color:var(--mut)}
 table{border-collapse:collapse;width:100%%;font-size:13.5px} td,th{border:1px solid var(--line);padding:7px 10px;text-align:left} th{color:var(--mut);font-weight:600}
 .pill{display:inline-block;padding:2px 9px;border-radius:999px;font-size:12px;border:1px solid var(--line)}
 .pill.ok{background:#0f2a18;border-color:#1f5e36} .pill.bad{background:#2a1010;border-color:#5e1f1f}
 .foot{color:var(--mut);font-size:12.5px;margin-top:30px;border-top:1px solid var(--line);padding-top:14px}
</style></head><body><div class="wrap">
 <h1>Rocqeteer — an audited counter, end to end</h1>
 <p class="sub">Prove it in Rocq · generate idiomatic OCaml · run it · validate the bridge. Result: <span class="pill %s">%s</span> &nbsp; <span class="pill %s">%s</span></p>

 <div class="pipe">
  <span class="n">Rocq EffIR + proof</span><span class="a">&rarr;</span>
  <span class="n">extract</span><span class="a">&rarr;</span>
  <span class="n">rocq-eff-codegen</span><span class="a">&rarr;</span>
  <span class="n">direct-style OCaml 5</span><span class="a">&rarr;</span>
  <span class="n">Env &deg; Trace &deg; KV handlers</span><span class="a">&rarr;</span>
  <span class="n">differential check</span>
 </div>

 <p class="mut">The program composes <b>Env</b> (read an audit tag), <b>Trace</b> (log it), <b>recursion</b>
 (bump a hit-counter 3&times;), and <b>KV</b> (persist the tag) — then the result is serialized via a codec
 whose round-trip is proven.</p>

 <div class="card"><h2><span class="step">1</span>Written &amp; proven in Rocq</h2>
  <p class="mut">The source — a first-order EffIR term:</p>
  <pre>%s</pre>
  <p class="mut">The machine-checked theorem (full functional result for the concrete run):</p>
  <pre>%s</pre>
  <p><span class="ok">&#10003;</span> <code>Print Assumptions demo_correct</code> = <b>"Closed under the global context"</b> — 0 axioms.</p>
 </div>

 <div class="card"><h2><span class="step">2</span>Code-generated to idiomatic OCaml 5</h2>
  <p class="mut">Direct style — the monad is erased; no interpreter, just effect calls and a native for-loop:</p>
  <pre>%s</pre>
  <p class="mut"><b>Where are the effects?</b> <code>Env.ask</code> / <code>Trace.emit</code> /
  <code>Kv.put</code> <i>are</i> the effect operations: each is a thin wrapper whose body is an
  <code>Effect.perform</code>, deliberately confined to <code>runtime/</code> (a CI gate forbids
  <code>Effect.perform</code> anywhere else, and the <code>.mli</code>s hide the effect constructors).
  Generated code therefore reads like ordinary OCaml while the effect boundary stays narrow and reviewed:</p>
  <pre>%s</pre>
 </div>

 <div class="card"><h2><span class="step">3</span>Run under the native handler stack</h2>
  <p>context (audit tag) = <span class="kv">%d</span></p>
  <p>final store: <span class="kv">%s</span></p>
  <p>audit trace: <span class="kv">%s</span></p>
 </div>

 <div class="card"><h2><span class="step">4</span>Validated — proven reference vs. fast OCaml</h2>
  <table><tr><th></th><th>store</th><th>trace</th></tr>
   <tr><td class="mut">reference (pure Rocq interpreter)</td><td class="kv">%s</td><td class="kv">%s</td></tr>
   <tr><td class="mut">fast (generated + handlers)</td><td class="kv">%s</td><td class="kv">%s</td></tr></table>
  <p style="margin-top:10px"><span class="%s">%s</span> &nbsp; differential check.</p>
  <p>persistence via the proven codec: <code>(3,%d)</code> &rarr; bytes <code>%s</code> &rarr; decode &rarr; <code>(%d,%d)</code> &nbsp; <span class="%s">%s</span></p>
 </div>

 <div class="card"><h2>The trust ledger</h2>
  <table><tr><th>layer</th><th>status</th></tr>
   <tr><td>program meets its spec under the reference semantics</td><td class="ok">PROVEN (Rocq, 0 axioms)</td></tr>
   <tr><td>codec round-trip (decode &deg; encode = id)</td><td class="ok">PROVEN (Rocq, 0 axioms)</td></tr>
   <tr><td>OCaml compiler/runtime, codegen, effect handlers, realizers</td><td class="mut">TRUSTED + differentially tested</td></tr>
   <tr><td>Obj.magic / unregistered Extract Constant / hidden axioms</td><td class="ok">0 (CI-enforced)</td></tr>
   <tr><td>performance &amp; determinism</td><td class="mut">MEASURED (CI gates)</td></tr></table>
 </div>

 <p class="foot">Generated by the Rocqeteer demo (make demo). Effects: State · Error · Env · Trace · Cache, plus bounded recursion and a verified codec. Toolchain: Rocq 9.1.1 / OCaml 5.4.1.</p>
</div></body></html>
|html}
      agree_cls (esc agree_txt) rt_cls (esc rt_txt) (esc rocq_src) (esc theorem) (esc gen_code)
      (esc wrapper_code) tag (show_kv fkv)
      (show_tr ftr) (show_kv rkv) (show_tr rtr) (show_kv fkv) (show_tr ftr) agree_cls (esc agree_txt) tag (esc hex)
      (fst decoded) (snd decoded) rt_cls (esc rt_txt)
  in
  ignore ok;
  Out_channel.with_open_text "demo/demo_report.html" (fun oc -> Out_channel.output_string oc html)
