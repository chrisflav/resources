import Resources.Invoice.Invoice
import Resources.Store.Contacts

/-!
# Rendering invoices

QR codes come from `qrencode` and PDFs from `xelatex`. Both are shelled out to,
because writing a QR encoder and a PDF writer is not the interesting part of
this system — though the QR encoder is a pleasant later project, and everything
here goes through `Qr.encode` so that swap is one function.
-/

namespace Resources

namespace Qr

/-- Where `qrencode` writes; `SVG`, `PNG`, `EPS`, `ANSIUTF8` and `UTF8` are the useful formats. -/
private def run (payload : String) (fmt : String) (out : System.FilePath)
    (level : String := "M") : IO Unit := do
  let res ← IO.Process.output
    { cmd := "qrencode"
      args := #["-t", fmt, "-l", level, "-o", out.toString, "--", payload] }
  if res.exitCode != 0 then
    throw <| IO.userError s!"qrencode failed ({res.exitCode}): {res.stderr}"

private def scratch (suffix : String) : IO System.FilePath := do
  let n ← freshId
  let dir : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  return dir / s!"resources-qr-{n}{suffix}"

/-- Encodes a payload as an SVG document. -/
def svg (payload : String) : IO String := do
  let p ← scratch ".svg"
  try
    run payload "SVG" p
    IO.FS.readFile p
  finally
    if ← p.pathExists then IO.FS.removeFile p

/-- Encodes a payload as PNG bytes. -/
def png (payload : String) : IO ByteArray := do
  let p ← scratch ".png"
  try
    run payload "PNG" p
    IO.FS.readBinFile p
  finally
    if ← p.pathExists then IO.FS.removeFile p

/-- Encodes a payload as EPS, for embedding in LaTeX. -/
def eps (payload : String) (out : System.FilePath) : IO Unit := run payload "EPS" out

/-- Encodes a payload as block characters, for printing in a terminal. -/
def ansi (payload : String) : IO String := do
  let p ← scratch ".txt"
  try
    run payload "UTF8" p
    IO.FS.readFile p
  finally
    if ← p.pathExists then IO.FS.removeFile p

/-- Whether `qrencode` is on the path. -/
def available : IO Bool := do
  try
    let res ← IO.Process.output { cmd := "qrencode", args := #["--version"] }
    return res.exitCode == 0
  catch _ => return false

end Qr

namespace Render

/-- Escapes text for inclusion in HTML. -/
def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

/-- Escapes text for inclusion in LaTeX. -/
def escapeTex (s : String) : String :=
  s.replace "\\" "\\textbackslash{}"
   |>.replace "&" "\\&" |>.replace "%" "\\%" |>.replace "$" "\\$"
   |>.replace "#" "\\#" |>.replace "_" "\\_" |>.replace "{" "\\{" |>.replace "}" "\\}"
   |>.replace "~" "\\textasciitilde{}" |>.replace "^" "\\textasciicircum{}"

/-- A self-contained HTML invoice with the payment QR inlined. -/
def html (inv : Invoice) (qrSvg : Option String := none) : String :=
  let rows := String.intercalate "\n" (inv.lines.map fun l =>
    s!"      <tr><td>{escapeHtml l.description}</td>" ++
    s!"<td class=\"n\">{l.quantity}</td>" ++
    s!"<td class=\"n\">{l.unitPrice.digits}</td>" ++
    s!"<td class=\"n\">{l.taxRate}</td>" ++
    s!"<td class=\"n\">{l.net.digits}</td></tr>")
  let qrBlock := match qrSvg with
    | some svg => s!"<div class=\"qr\">{svg}<p>Scan to pay</p></div>"
    | none => ""
  let noteBlock := match inv.note with
    | some n => s!"<p class=\"note\">{escapeHtml n}</p>"
    | none => ""
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\n" ++
  s!"<title>Invoice {inv.number}</title>\n" ++
  "<style>
  :root { --ink:#141b1a; --muted:#566764; --rule:#dbe4e1; --accent:#0e6e64; }
  body { font: 14px/1.55 'IBM Plex Serif', Georgia, serif; color: var(--ink);
         max-width: 46rem; margin: 3rem auto; padding: 0 1.5rem; background: #fff; }
  h1 { font-family: 'IBM Plex Sans', system-ui, sans-serif; font-size: 1.6rem; margin: 0 0 .2rem; }
  .meta { color: var(--muted); font-size: .85rem; margin-bottom: 2rem; }
  table { border-collapse: collapse; width: 100%; margin: 1.5rem 0; }
  th, td { text-align: left; padding: .45rem .6rem; border-bottom: 1px solid var(--rule); }
  th { font: 600 .72rem/1.4 'IBM Plex Mono', monospace; text-transform: uppercase;
       letter-spacing: .08em; color: var(--muted); }
  td.n, th.n { text-align: right; font-variant-numeric: tabular-nums; }
  tfoot td { border-bottom: none; }
  tfoot tr.total td { border-top: 2px solid var(--ink); font-weight: 600; }
  .qr { margin: 2rem 0; text-align: center; }
  .qr svg { width: 170px; height: 170px; }
  .qr p { font: .75rem 'IBM Plex Mono', monospace; color: var(--muted); }
  .ref { font-family: 'IBM Plex Mono', monospace; }
  .note { color: var(--muted); font-size: .9rem; }
  </style></head><body>\n" ++
  s!"<h1>Invoice {escapeHtml inv.number}</h1>\n" ++
  s!"<p class=\"meta\">Issued {inv.issued.toIso} · due {inv.due.toIso} · " ++
  s!"status {inv.status.toString}<br>To: {escapeHtml inv.payerName}<br>" ++
  s!"Reference: <span class=\"ref\">{escapeHtml inv.reference}</span></p>\n" ++
  "<table><thead><tr><th>Description</th><th class=\"n\">Qty</th>" ++
  "<th class=\"n\">Unit</th><th class=\"n\">Tax</th>" ++
  s!"<th class=\"n\">Net {inv.commodity.code}</th>" ++
  "</tr></thead><tbody>\n" ++ rows ++ "\n</tbody><tfoot>" ++
  s!"<tr><td colspan=\"4\">Net</td><td class=\"n\">{inv.net.digits}</td></tr>" ++
  s!"<tr><td colspan=\"4\">Tax</td><td class=\"n\">{inv.tax.digits}</td></tr>" ++
  s!"<tr class=\"total\"><td colspan=\"4\">Total {inv.commodity.code}</td>" ++
  s!"<td class=\"n\">{inv.total.digits}</td></tr>" ++
  "</tfoot></table>\n" ++ qrBlock ++ "\n" ++ noteBlock ++
  s!"<p class=\"meta\">Payable to {escapeHtml inv.payment.describe}</p>\n" ++
  "</body></html>"

/-- A LaTeX source document; `qrFile` is an EPS or PDF graphic to include. -/
def latex (inv : Invoice) (qrFile : Option String := none) : String :=
  let nl := "\n"
  let br := " \\\\" ++ nl
  let rows := String.join (inv.lines.map fun l =>
    escapeTex l.description ++ " & " ++ escapeTex l.quantity ++ " & " ++
    escapeTex l.unitPrice.digits ++ " & " ++ escapeTex l.taxRate ++ " & " ++
    escapeTex l.net.digits ++ br)
  let qrBlock := match qrFile with
    | some f =>
      "\\begin{center}" ++ nl ++
      "\\includegraphics[width=4cm]{" ++ f ++ "}" ++ br ++
      "{\\small Scan to pay}" ++ nl ++ "\\end{center}" ++ nl
    | none => ""
  String.join [
    "\\documentclass[11pt,a4paper]{article}", nl,
    "\\usepackage{fontspec}", nl,
    "\\usepackage{graphicx}", nl,
    "\\usepackage[margin=2.5cm]{geometry}", nl,
    "\\usepackage{booktabs}", nl,
    "\\pagestyle{empty}", nl,
    "\\begin{document}", nl,
    "{\\LARGE\\bfseries Invoice ", escapeTex inv.number, "}", br,
    "Issued ", inv.issued.toIso, " \\quad Due ", inv.due.toIso, br,
    "To: ", escapeTex inv.payerName, br,
    "Reference: \\texttt{", escapeTex inv.reference, "}", br, "[1em]", nl,
    "\\begin{tabular}{@{}p{7cm}rrrr@{}}", nl,
    "\\toprule", nl,
    "Description & Qty & Unit & Tax & Net", br,
    "\\midrule", nl,
    rows,
    "\\midrule", nl,
    "\\multicolumn{4}{@{}l}{Net} & ", inv.net.digits, br,
    "\\multicolumn{4}{@{}l}{Tax} & ", inv.tax.digits, br,
    "\\midrule", nl,
    "\\multicolumn{4}{@{}l}{\\bfseries Total ", inv.commodity.code, "} & \\bfseries ",
      inv.total.digits, br,
    "\\bottomrule", nl,
    "\\end{tabular}", br, "[1.5em]", nl,
    qrBlock,
    "\\vfill", nl,
    "{\\small Payable to ", escapeTex inv.payment.describe, "}", nl,
    "\\end{document}", nl]

/-- Renders an invoice to PDF via `xelatex`, writing the result to `out`. -/
def pdf (inv : Invoice) (out : System.FilePath) : IO Unit := do
  let tmpRoot : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let dir := tmpRoot / s!"resources-inv-{← freshId}"
  IO.FS.createDirAll dir
  try
    let qrName := "payment-qr.eps"
    let qrFile ← match inv.qrPayload with
      | .ok payload => do
        Qr.eps payload (dir / qrName)
        pure (some qrName)
      | .error _ => pure none
    IO.FS.writeFile (dir / "invoice.tex") (latex inv qrFile)
    let res ← IO.Process.output
      { cmd := "xelatex"
        args := #["-interaction=nonstopmode", "-halt-on-error", "invoice.tex"]
        cwd := dir }
    if !(← (dir / "invoice.pdf").pathExists) then
      throw <| IO.userError s!"xelatex failed:\n{(res.stdout.takeEnd 2000)}"
    let bytes ← IO.FS.readBinFile (dir / "invoice.pdf")
    IO.FS.writeBinFile out bytes
  finally
    IO.FS.removeDirAll dir <|> pure ()

end Render

/-! ## Handing an invoice to a person -/

namespace Invoices

/-- Percent-encodes a mailto component. `keep` names characters to leave alone. -/
private def escWith (keep : List Char) (s : String) : String := Id.run do
  let hexDigits := "0123456789ABCDEF".toList.toArray
  let mut out := ""
  for b in s.toUTF8 do
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~' || keep.contains c then
      out := out.push c
    else out := out.push '%' |>.push hexDigits[b.toNat / 16]! |>.push hexDigits[b.toNat % 16]!
  return out

/-- The address part: `@` and `+` are legal in an addr-spec and clients expect them raw. -/
private def escAddress (s : String) : String := escWith ['@', '+'] s

/-- Percent-encodes a mailto component. -/
private def esc (s : String) : String := Id.run do
  let hexDigits := "0123456789ABCDEF".toList.toArray
  let mut out := ""
  for b in s.toUTF8 do
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~' then out := out.push c
    else out := out.push '%' |>.push hexDigits[b.toNat / 16]! |>.push hexDigits[b.toNat % 16]!
  return out

/--
A `mailto:` link that sends an invoice to whoever owes it.

The body is the cost overview in plain text — line by line, with the total, the
IBAN and the reference — because that is what the recipient can act on without
opening anything. The PDF is still there if they want it.
-/
def mailto (ctx : Ctx) (inv : Invoice) : IO String := do
  -- The address comes from your address book, not from anything stored here.
  let contact ← Contacts.byName? ctx inv.payerName
  let address := (contact.bind (·.email)).getD ""
  let lines := String.intercalate "\n" (inv.lines.map fun l =>
    s!"  {Str.padRight l.description 46} {Str.padLeft l.net.digits 10} {inv.commodity.code}")
  let body := String.intercalate "\n" [
    s!"Hallo {inv.payerName},",
    "",
    s!"anbei die Kostenaufstellung zu Rechnung {inv.number} vom {inv.issued.toIso}:",
    "",
    lines,
    "",
    s!"  {Str.padRight "Gesamt" 46} {Str.padLeft inv.total.digits 10} {inv.commodity.code}",
    "",
    s!"Zahlbar bis {inv.due.toIso} an {inv.payment.describe}",
    s!"Verwendungszweck: {inv.reference}",
    "",
    "Viele Grüße"]
  let subject := esc s!"Kostenaufstellung {inv.number}"
  return s!"mailto:{escAddress address}?subject={subject}&body={esc body}"

end Invoices

end Resources
