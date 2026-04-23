-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import DevTool.Toolkit.Common

/-!
# symbol-map サブコマンド

S2IL プロジェクトの public 宣言を JSONL 形式で出力する。
エージェントがシンボル名からファイル・種別・タグに O(1) でアクセスできるようにする。
-/

open Lean

namespace DevTool.Toolkit.SymbolMap

open DevTool.Toolkit.Common

/-- symbol-map サブコマンドの設定 -/
structure Config where
    /-- 対象モジュールプレフィックス -/
    nsPrefix : String := "S2IL"
    /-- 出力ファイルパス（None なら stdout） -/
    outputPath : Option String := none

/-- コマンドライン引数を再帰的に解析する -/
def parseArgs : List String → Config → Config
    | "--ns" :: ns :: rest, cfg => parseArgs rest { cfg with nsPrefix := ns }
    | "--output" :: p :: rest, cfg => parseArgs rest { cfg with outputPath := some p }
    | "--out" :: p :: rest, cfg => parseArgs rest { cfg with outputPath := some p }
    | _ :: rest, cfg => parseArgs rest cfg
    | [], cfg => cfg

/-- 宣言名・モジュール名からタグを自動推定する（簡易ヒューリスティック）。
    エージェントが「等変性」「spb」などの概念で絞り込めるよう補助する。 -/
def inferTags (name : Name) (modName : Name) : Array String := Id.run do
    let s := toString name
    let m := toString modName
    let mut tags : Array String := #[]
    if s.containsSubstr "rotate180" || s.containsSubstr "Rotate180" then tags := tags.push "r180"
    if s.containsSubstr "rotateCW" || s.containsSubstr "RotateCW" then tags := tags.push "rCW"
    if s.containsSubstr "_comm" || m.containsSubstr "Equivariance" || s.containsSubstr "equivar" then
        tags := tags.push "equivariance"
    if s.containsSubstr "shouldProcessBefore" || s.containsSubstr "_spb" then
        tags := tags.push "spb"
    if s.containsSubstr "sortFallingUnits" then tags := tags.push "sort"
    if s.containsSubstr "floatingUnits" then tags := tags.push "floating"
    if (s.containsSubstr "process" || s.containsSubstr "Process") &&
       !s.containsSubstr "shouldProcess" then
        tags := tags.push "process"
    if s.containsSubstr "IsSettled" || s.containsSubstr "isSettled" then
        tags := tags.push "settled"
    if m.containsSubstr "PermInvariance" then tags := tags.push "perm"
    if m.containsSubstr "CommExt" then tags := tags.push "comm"
    if m.containsSubstr "FoldlBridge" then tags := tags.push "bridge"
    return tags

/-- シンボル位置 DB を JSONL 形式で出力する。
    各行が 1 シンボルの JSON オブジェクトで、エージェントがシンボル名からファイル・種別・タグに
    O(1) でアクセスできるようにする。
    private 宣言は除外（public API のみを対象とする）。
    NOTE: 行番号は Environment API からは取得できない（宣言範囲は .ilean に格納されており
    importModules でロードする .olean には含まれないため）。行番号が必要な場合は
    grep_search でシンボル名を検索すること。 -/
def formatSymbolMap (nodes : Array Node) : String :=
    let lines := nodes.filterMap fun n =>
        if n.isPrivate then none
        else
            let filePath := filePathFromModule n.moduleName
            let tags := inferTags n.name n.moduleName
            let baseFields : List (String × Json) := [
                ("symbol", .str (toString n.name)),
                ("kind",   .str (toString n.kind)),
                ("file",   .str filePath)
            ]
            let sorryFields : List (String × Json) :=
                if n.hasSorry then [("sorry", .bool true)] else []
            let tagFields : List (String × Json) :=
                if !tags.isEmpty then
                    [("tags", Json.arr (tags.map fun t => .str t))]
                else []
            some (Json.mkObj (baseFields ++ sorryFields ++ tagFields)).compress
    String.intercalate "\n" lines.toList

/-- symbol-map サブコマンドのエントリポイント -/
def run (env : Environment) (args : List String) : IO Unit := do
    let cfg := parseArgs args {}
    let nodes := buildNodes env cfg.nsPrefix false false false
    let output := formatSymbolMap nodes

    -- 統計情報を stderr に出力
    let publicCount := (nodes.filter (!·.isPrivate)).size
    IO.eprintln s!"=== SYMBOL MAP ==="
    IO.eprintln s!"  symbols: {publicCount}"
    IO.eprintln s!"=== END SYMBOL MAP ==="

    match cfg.outputPath with
    | some path => IO.FS.writeFile ⟨path⟩ output
    | none => IO.print output

end DevTool.Toolkit.SymbolMap
