# Knowledge Base — S2IL 証明ナレッジ

本プロジェクトの Lean 4 証明作業で得られた知見をまとめたナレッジベース。

証明やコーディングで行き詰まった場合はまずここを参照すること。

---

## ファイル一覧

### 汎用 Tips（常に参照価値あり）

| ファイル | 概要 |
|---|---|
| [lean-proof-tips.md](lean-proof-tips.md) | Lean 4 証明の実践的 Tips。タクティク使い分け（`rw` vs `simp only`、`decide`、`<;>`）・`List.mapM` 回避・`String` 証明の注意点・帰納法パターン・`rcases` など |
| [mathlib-batteries-tips.md](mathlib-batteries-tips.md) | Mathlib / Batteries 活用ノウハウ。利用実績のある補題（`List.map_set`・`BEq.comm` 等）・型クラス（`Std.Commutative` 等）・置換パターン・`simp` 最適化・`List.Perm` |
| [string-roundtrip-proof.md](string-roundtrip-proof.md) | `ofString? (toString x) = some x` 形式のラウンドトリップ定理の証明パターン。`String.splitOn` / `intercalate` の展開不可問題、`List Char` レベルの完全自前実装戦略 |

### ドメイン固有の証明分析（特定機能の証明に取り組む際に参照）

| ファイル | 概要 |
|---|---|
| [bfs-equivariance-proof.md](bfs-equivariance-proof.md) | `CrystalBond.bfs` の 180° 回転等変性証明の知見。BFS のリスト等号が探索順序依存で偽になる問題・`fuel` 帰納法での `show` テクニック・`clearPositions` レベルへの引き上げ |
| [gravity-equivariance-analysis.md](gravity-equivariance-analysis.md) | `Gravity.lean` の `process_rotate180` 証明の知見。`shouldProcessBefore` の非反対称性・`sortFU` の偽定理反例・`insertSorted` のグリーディ動作特性・`foldl` 交換法則パターン |
| [settle-foldl-eq-analysis.md](settle-foldl-eq-analysis.md) | `settle_foldl_eq` sorry の詳細分析。証明難航の原因・偽定理の経緯・現在の残 sorry と証明計画（DAG 選択肢 A/B/C） |

---

## エージェント向け編集ガイダンス

### どのファイルに追記するか

| 知見の種類 | 追記先 |
|---|---|
| Lean 4 のタクティク・構文・型クラスに関する一般的な使い分けや落とし穴 | `lean-proof-tips.md` |
| Mathlib / Batteries の具体的な補題名・型クラス・置換パターン | `mathlib-batteries-tips.md` |
| `String` ↔ `List Char` ブリッジや `ofString?/toString` ラウンドトリップの実装戦略 | `string-roundtrip-proof.md` |
| BFS/クリスタル結合の等変性に関するパターン・アンチパターン | `bfs-equivariance-proof.md` |
| Gravity の `process_rotate180` 証明・`shouldProcessBefore`・`sortFU`・`foldl` 等変性 | `gravity-equivariance-analysis.md` |
| `settle_foldl_eq` 証明の詳細分析・偽定理の記録・証明計画  | `settle-foldl-eq-analysis.md` |
| 上記に当てはまらない新しいドメイン固有の証明分析 | 新規ファイルを作成しこの README に追記 |

### 汎用 Tips とドメイン固有分析の書き分け基準

- **汎用 Tips** (`lean-proof-tips.md` / `mathlib-batteries-tips.md`):
  - 「Lean 4 全般で起こりうる問題の根本原因 + 一行で言える代替手段」の形式
  - 具体的なコードは最小限の例示のみ。本プロジェクト固有の型名は出さない
  - 例: `by_cases` が効かない → `cases` を使う、`List.filterMap_cons` はない → `simp only [List.filterMap]`

- **ドメイン固有分析** (`bfs-equivariance-proof.md` 等):
  - 「なぜ詰まったか（失敗したアプローチ）+ 何が正しかったか（成功したアプローチ）」の形式
  - 本プロジェクトの関数名・定理名を具体的に使ってよい
  - 偽定理と判明したものは残して記録すること（同じ罠に再度はまらないため）

### 追記の粒度基準

- **追記する**: 1 時間以上詰まった問題、「知っていれば 5 分で解決できた」パターン
- **追記しない**: 公式ドキュメントに書いてある内容、1 回しか使わない実装の詳細
- **新ファイルを作る**: 新しい `S2IL/Behavior/` モジュールの大規模な証明分析が生まれた場合。ファイル名は `<対象機能>-<証明種別>.md`（例: `painter-equivariance-analysis.md`）

---

## 関連リンク

- [docs/gravity-rotate180-proof-plan.md](../gravity-rotate180-proof-plan.md) — `process_rotate180` 証明の現在の計画
- [.github/skills/](../../.github/skills/) — 証明ワークフロー支援 Skills（lean-proof-planning、lean-proof-progress 等）
