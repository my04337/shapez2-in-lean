-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import DevTool.Toolkit.Common

/-!
# proof-stats サブコマンド

モジュール別の定理数・定義数・sorry 数・axiom 数をテーブルまたは JSON 形式で出力する。
マイルストーン追跡やプロジェクト状況の俯瞰に利用する。
-/

open Lean

namespace DevTool.Toolkit.ProofStats

open DevTool.Toolkit.Common

/-- proof-stats サブコマンドの設定 -/
structure Config where
    /-- 対象モジュールプレフィックス -/
    nsPrefix : String := "S2IL"
    /-- JSON 形式で出力するか -/
    jsonOutput : Bool := false
    /-- 出力ファイルパス（None なら stdout） -/
    outputPath : Option String := none

/-- コマンドライン引数を再帰的に解析する -/
def parseArgs : List String → Config → Config
    | "--ns" :: ns :: rest, cfg => parseArgs rest { cfg with nsPrefix := ns }
    | "--json" :: rest, cfg => parseArgs rest { cfg with jsonOutput := true }
    | "--output" :: p :: rest, cfg => parseArgs rest { cfg with outputPath := some p }
    | _ :: rest, cfg => parseArgs rest cfg
    | [], cfg => cfg

/-- モジュール別の統計情報 -/
structure ModuleStats where
    moduleName : String
    theorems : Nat := 0
    defs : Nat := 0
    axioms : Nat := 0
    opaques : Nat := 0
    inductives : Nat := 0
    sorries : Nat := 0

/-- ノード一覧からモジュール別統計を計算する -/
def computeStats (nodes : Array Node) : Array ModuleStats := Id.run do
    -- モジュール名ごとに集約（RBMap で管理）
    let mut statsMap : Lean.RBMap String ModuleStats compare := Lean.RBMap.empty
    for node in nodes do
        let modStr := toString node.moduleName
        let mut stats := (statsMap.find? modStr).getD { moduleName := modStr }
        match node.kind with
        | .theorem => stats := { stats with theorems := stats.theorems + 1 }
        | .def => stats := { stats with defs := stats.defs + 1 }
        | .axiom => stats := { stats with axioms := stats.axioms + 1 }
        | .opaque => stats := { stats with opaques := stats.opaques + 1 }
        | .inductive => stats := { stats with inductives := stats.inductives + 1 }
        if node.hasSorry then
            stats := { stats with sorries := stats.sorries + 1 }
        statsMap := statsMap.insert modStr stats
    -- RBMap はキーでソート済み
    statsMap.toList.toArray.map (·.2)

/-- テーブル形式で出力する -/
def formatTable (stats : Array ModuleStats) : String := Id.run do
    let mut out := "| モジュール | 定理 | 定義 | axiom | sorry |\n"
    out := out ++ "|---|---|---|---|---|\n"
    let mut totalThm : Nat := 0
    let mut totalDef : Nat := 0
    let mut totalAxiom : Nat := 0
    let mut totalSorry : Nat := 0
    for s in stats do
        let sorryMark := if s.sorries > 0 then s!" **{s.sorries}**" else " 0"
        out := out ++ s!"| {s.moduleName} | {s.theorems} | {s.defs} | {s.axioms} |{sorryMark} |\n"
        totalThm := totalThm + s.theorems
        totalDef := totalDef + s.defs
        totalAxiom := totalAxiom + s.axioms
        totalSorry := totalSorry + s.sorries
    out := out ++ s!"| **合計** | **{totalThm}** | **{totalDef}** | **{totalAxiom}** | **{totalSorry}** |\n"
    return out

/-- Nat を Json 数値に変換するヘルパー -/
private def natJson (n : Nat) : Json := Json.num n

def formatJson (stats : Array ModuleStats) : String :=
    let arr := stats.map fun s =>
        Json.mkObj [
            ("module", .str s.moduleName),
            ("theorems", natJson s.theorems),
            ("defs", natJson s.defs),
            ("axioms", natJson s.axioms),
            ("opaques", natJson s.opaques),
            ("inductives", natJson s.inductives),
            ("sorries", natJson s.sorries)
        ]
    let root := Json.mkObj [
        ("modules", Json.arr arr),
        ("total", Json.mkObj [
            ("theorems", natJson (stats.foldl (fun acc s => acc + s.theorems) 0)),
            ("defs", natJson (stats.foldl (fun acc s => acc + s.defs) 0)),
            ("axioms", natJson (stats.foldl (fun acc s => acc + s.axioms) 0)),
            ("sorries", natJson (stats.foldl (fun acc s => acc + s.sorries) 0))
        ])
    ]
    root.pretty

/-- proof-stats サブコマンドのエントリポイント -/
def run (env : Environment) (args : List String) : IO Unit := do
    let cfg := parseArgs args {}
    -- private 宣言も含め、全宣言種別を対象とする
    let nodes := buildNodes env cfg.nsPrefix true false false
    let stats := computeStats nodes

    -- サマリーを stderr に出力
    let totalThm := stats.foldl (fun acc s => acc + s.theorems) 0
    let totalSorry := stats.foldl (fun acc s => acc + s.sorries) 0
    IO.eprintln "=== PROOF STATS ==="
    IO.eprintln s!"  modules: {stats.size}"
    IO.eprintln s!"  theorems: {totalThm}"
    IO.eprintln s!"  sorries: {totalSorry}"
    IO.eprintln "=== END PROOF STATS ==="

    let output := if cfg.jsonOutput then formatJson stats else formatTable stats

    match cfg.outputPath with
    | some path => IO.FS.writeFile ⟨path⟩ output
    | none => IO.print output

end DevTool.Toolkit.ProofStats
