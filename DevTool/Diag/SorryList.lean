-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import Lean.Data.Json

/-!
# sorry-list サブコマンド

`.lake/build-diagnostics.jsonl` を読み込み、sorry エントリを構造化出力する。
S2IL ライブラリに依存しないため、S2IL にビルドエラーがある状態でも利用可能。
-/

namespace DevTool.Diag.SorryList

/-- JSONL 1 行から解析した診断エントリ -/
structure DiagEntry where
    file : String
    line : Nat
    col : Nat
    severity : String
    message : String
    isSorry : Bool
    deriving Inhabited

/-- JSON オブジェクトから DiagEntry を復元する -/
def DiagEntry.fromJson? (j : Lean.Json) : Option DiagEntry := do
    let file ← j.getObjValAs? String "file" |>.toOption
    let line ← j.getObjValAs? Nat "line" |>.toOption
    let col ← j.getObjValAs? Nat "col" |>.toOption
    let severity ← j.getObjValAs? String "severity" |>.toOption
    let message ← j.getObjValAs? String "message" |>.toOption
    let isSorry := (j.getObjValAs? Bool "isSorry" |>.toOption).getD false
    some { file, line, col, severity, message, isSorry }

/-- DiagEntry を JSON オブジェクトに変換する -/
def DiagEntry.toJson (e : DiagEntry) : Lean.Json :=
    Lean.Json.mkObj [
        ("file", .str e.file),
        ("line", .num e.line),
        ("col", .num e.col),
        ("message", .str e.message)
    ]

/-- 診断 JSONL ファイルのパスを解決する。
    セッション固有ファイルが存在すればそちらを優先する。 -/
def resolveDiagPath : IO System.FilePath := do
    let lakeDir : System.FilePath := ".lake"
    let sessionIdFile := lakeDir / "session-id.tmp"
    if ← sessionIdFile.pathExists then
        let sid := (← IO.FS.readFile sessionIdFile).trimAscii.toString
        if !sid.isEmpty then
            let sessionPath := lakeDir / s!"build-diagnostics-{sid}.jsonl"
            if ← sessionPath.pathExists then
                return sessionPath
    return lakeDir / "build-diagnostics.jsonl"

/-- 診断 JSONL ファイルから sorry エントリを抽出する -/
def loadSorries (path : System.FilePath) : IO (Array DiagEntry) := do
    unless ← path.pathExists do
        throw <| IO.userError s!"診断ファイルが見つかりません: {path}\nlake build を先に実行してください。"
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n" |>.filter (!·.isEmpty)
    let mut result : Array DiagEntry := #[]
    for line in lines do
        match Lean.Json.parse line with
        | .ok j =>
            if let some entry := DiagEntry.fromJson? j then
                if entry.isSorry then
                    result := result.push entry
        | .error _ => continue
    return result

/-- sorry 一覧をテーブル形式で出力する -/
def formatTable (entries : Array DiagEntry) : String := Id.run do
    if entries.isEmpty then
        return "sorry なし"
    let mut out := s!"sorry: {entries.size} 件\n"
    out := out ++ "\n| # | ファイル | 行:列 |\n"
    out := out ++ "|---|---|---|\n"
    for i in [:entries.size] do
        let e := entries[i]!
        out := out ++ s!"| {i + 1} | {e.file} | {e.line}:{e.col} |\n"
    return out

/-- sorry 一覧を JSONL 形式で出力する -/
def formatJsonl (entries : Array DiagEntry) : String :=
    let lines := entries.map fun e => e.toJson.compress
    String.intercalate "\n" lines.toList

/-- sorry-list サブコマンドのエントリポイント -/
def run (args : List String) : IO Unit := do
    let jsonMode := args.contains "--json"
    let diagPath ← resolveDiagPath
    let sorries ← loadSorries diagPath

    -- サマリーを stderr に出力
    IO.eprintln s!"=== SORRY LIST ==="
    IO.eprintln s!"source: {diagPath}"
    IO.eprintln s!"sorry: {sorries.size}"
    IO.eprintln s!"=== END SORRY LIST ==="

    -- 本体を stdout に出力
    if jsonMode then
        IO.print (formatJsonl sorries)
    else
        IO.print (formatTable sorries)

end DevTool.Diag.SorryList
