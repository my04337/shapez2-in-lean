-- SPDX-FileCopyrightText: 2026 my04337
-- SPDX-License-Identifier: MIT

import DevTool.Toolkit.Common

/-!
# depgraph サブコマンド

S2IL プロジェクト内の定理・定義間の依存関係を
Lean の `Environment` API から抽出し、Mermaid または JSON 形式で出力する。
-/

open Lean

namespace DevTool.Toolkit.DepGraph

open DevTool.Toolkit.Common

/-- depgraph サブコマンドの設定 -/
structure Config where
    /-- private 宣言を含めるか -/
    includePrivate : Bool := false
    /-- JSON 形式で出力するか（false なら Mermaid） -/
    jsonOutput : Bool := false
    /-- 対象モジュールプレフィックス -/
    nsPrefix : String := "S2IL"
    /-- 定理のみ表示するか -/
    theoremsOnly : Bool := false
    /-- 出力ファイルパス（None なら stdout） -/
    outputPath : Option String := none
    /-- 起点となる宣言名 -/
    rootDecl : Option String := none
    /-- 起点を逆向きにたどるか -/
    rootReverse : Bool := false
    /-- sorry を持つ宣言のみ表示するか -/
    sorriesOnly : Bool := false

/-- コマンドライン引数を再帰的に解析する -/
def parseArgs : List String → Config → Config
    | "--private" :: rest, cfg => parseArgs rest { cfg with includePrivate := true }
    | "--json" :: rest, cfg => parseArgs rest { cfg with jsonOutput := true }
    | "--ns" :: ns :: rest, cfg => parseArgs rest { cfg with nsPrefix := ns }
    | "--theorems-only" :: rest, cfg => parseArgs rest { cfg with theoremsOnly := true }
    | "--output" :: p :: rest, cfg => parseArgs rest { cfg with outputPath := some p }
    | "--root" :: decl :: rest, cfg => parseArgs rest { cfg with rootDecl := some decl }
    | "--root-reverse" :: rest, cfg => parseArgs rest { cfg with rootReverse := true }
    | "--sorry-only" :: rest, cfg => parseArgs rest { cfg with sorriesOnly := true }
    | _ :: rest, cfg => parseArgs rest cfg
    | [], cfg => cfg

-- ============================================================
-- 起点フィルタ
-- ============================================================

/-- 指定した起点宣言から到達可能なノード・エッジに絞り込む。
    reverse = false: 起点が依存するすべての宣言（依存先を辿る）
    reverse = true:  起点を利用するすべての宣言（依存元を辿る） -/
def filterByRoot (rootDecl : Name) (nodes : Array Node) (edges : Array (Name × Name))
        (reverse : Bool) : Array Node × Array (Name × Name) := Id.run do
    let mut adj : NameMap (Array Name) := {}
    for (src, tgt) in edges do
        if reverse then
            let cur := (adj.find? tgt).getD #[]
            adj := adj.insert tgt (cur.push src)
        else
            let cur := (adj.find? src).getD #[]
            adj := adj.insert src (cur.push tgt)
    -- BFS で到達可能ノードを収集
    let mut visited : NameSet := {}
    let mut queue : Array Name := #[rootDecl]
    visited := visited.insert rootDecl
    while queue.size > 0 do
        let cur := queue[0]!
        queue := queue.extract 1 queue.size
        for next in (adj.find? cur).getD #[] do
            unless visited.contains next do
                visited := visited.insert next
                queue := queue.push next
    let filtNodes := nodes.filter fun n => visited.contains n.name
    let filtEdges := edges.filter fun (s, t) => visited.contains s && visited.contains t
    return (filtNodes, filtEdges)

-- ============================================================
-- Name を Mermaid 安全な ID 文字列に変換する
-- ============================================================

def sanitizeId (n : Name) : String :=
    let s := toString n
    s.toList.map (fun c =>
        if c.isAlphanum || c == '_' then c else '_'
    ) |> String.ofList

-- ============================================================
-- Mermaid 出力
-- ============================================================

def formatMermaid (nodes : Array Node) (edges : Array (Name × Name)) : String :=
    Id.run do
    let mut out := "graph TD\n"
    let moduleList := (nodes.map (·.moduleName)).toList.eraseDups
    for modName in moduleList do
        let modNodes := nodes.filter (·.moduleName == modName)
        out := out ++ s!"    subgraph {modName}\n"
        for node in modNodes do
            let id := sanitizeId node.name
            let label := toString node.name
            let kindStr := toString node.kind
            if node.hasSorry then
                out := out ++ s!"        {id}[\"{label}  sorry {kindStr}\"]\n"
                out := out ++ s!"        style {id} fill:#ffcccc,stroke:#ff0000\n"
            else
                out := out ++ s!"        {id}[\"{label}  {kindStr}\"]\n"
        out := out ++ "    end\n"
    for (src, tgt) in edges do
        out := out ++ s!"    {sanitizeId src} --> {sanitizeId tgt}\n"
    return out

-- ============================================================
-- JSON 出力
-- ============================================================

def formatJson (nodes : Array Node) (edges : Array (Name × Name)) : String :=
    let nodeArr := nodes.map fun n =>
        Json.mkObj [
            ("name", .str (toString n.name)),
            ("kind", .str (toString n.kind)),
            ("module", .str (toString n.moduleName)),
            ("sorry", .bool n.hasSorry),
            ("private", .bool n.isPrivate)
        ]
    let edgeArr := edges.map fun (s, t) =>
        Json.mkObj [
            ("from", .str (toString s)),
            ("to", .str (toString t))
        ]
    let root := Json.mkObj [
        ("nodes", Json.arr nodeArr),
        ("edges", Json.arr edgeArr)
    ]
    root.pretty

-- ============================================================
-- メイン実行
-- ============================================================

/-- depgraph サブコマンドのエントリポイント -/
def run (env : Environment) (args : List String) : IO Unit := do
    let cfg := parseArgs args {}

    -- グラフ構築
    let nodes := buildNodes env cfg.nsPrefix cfg.includePrivate cfg.sorriesOnly cfg.theoremsOnly
    let edges := buildEdges env nodes

    -- 起点フィルタの適用
    let (outNodes, outEdges) ← match cfg.rootDecl with
        | none => pure (nodes, edges)
        | some rootStr =>
            let rootName := rootStr.toName
            if nodes.any (·.name == rootName) then
                pure (filterByRoot rootName nodes edges cfg.rootReverse)
            else do
                IO.eprintln s!"Warning: root declaration '{rootStr}' not found in graph."
                pure (nodes, edges)

    -- sorry-only フィルタの適用
    let (outNodes, outEdges) :=
        if cfg.sorriesOnly then
            let sorryOnlyNames : NameSet :=
                outNodes.foldl (fun (s : NameSet) n => if n.hasSorry then s.insert n.name else s) {}
            (outNodes.filter (·.hasSorry),
             outEdges.filter fun ⟨s, t⟩ => sorryOnlyNames.contains s && sorryOnlyNames.contains t)
        else
            (outNodes, outEdges)

    -- 統計情報を stderr に出力
    let sorryNodesArr := outNodes.filter (·.hasSorry)
    let sorryCount := sorryNodesArr.size
    let sorryNamesSet : NameSet := sorryNodesArr.foldl (fun (s : NameSet) n => s.insert n.name) {}
    let thmCount := (outNodes.filter fun n => n.kind == .theorem).size
    let independentSorryCount := (sorryNodesArr.filter fun n =>
        !outEdges.any fun ⟨s, t⟩ => s == n.name && sorryNamesSet.contains t).size
    IO.eprintln "=== DEPGRAPH STATISTICS ==="
    IO.eprintln s!"  nodes: {outNodes.size} (theorems: {thmCount}, other: {outNodes.size - thmCount})"
    IO.eprintln s!"  edges: {outEdges.size}"
    if sorryCount > 0 then
        IO.eprintln s!"  sorry: {sorryCount} (independent: {independentSorryCount})"
    IO.eprintln "=== END STATISTICS ==="

    -- 出力フォーマットの選択
    let output :=
        if cfg.jsonOutput
        then formatJson outNodes outEdges
        else formatMermaid outNodes outEdges

    -- ファイルまたは stdout に出力
    match cfg.outputPath with
    | some path => IO.FS.writeFile ⟨path⟩ output
    | none => IO.print output

end DevTool.Toolkit.DepGraph
