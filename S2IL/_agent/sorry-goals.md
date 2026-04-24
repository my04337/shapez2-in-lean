# Sorry Goals Snapshot

> 自動生成: 2026-04-25 13:28:35
> ソース: `.lean` ファイル直接スキャン (build diagnostics に非依存)
> スキャン対象: S2IL
> 用途: sorry 位置の含む宣言シグネチャを REPL 起動なしで取得する

sorry 件数: **1**

## 1. S2IL/Operations/Swapper.lean:30

- 宣言: `Shape.swap_rotate180_comm` (*theorem* at L27)

```lean
theorem Shape.swap_rotate180_comm (s1 s2 : Shape) :
    Shape.swap s1.rotate180 s2.rotate180 =
      ((Shape.swap s1 s2).2.rotate180, (Shape.swap s1 s2).1.rotate180) := by
```

sorry 行: `sorry -- Phase C/D で証明。combineHalves_rotate180 axiom が必要`

