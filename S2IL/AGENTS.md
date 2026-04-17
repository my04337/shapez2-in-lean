# S2IL Lean コーディング規約と証明ワークフロー

> このファイルは `S2IL/` 配下のコード作業時に自動適用される（`chat.useNestedAgentsMdFiles` 有効時）。
> プロジェクト全体の規約は [AGENTS.md](../AGENTS.md) を参照。

## Lean 4 命名規則（S2IL 固有）

> **一般的な Lean 4 / Mathlib 命名規則**: [`docs/lean/naming-conventions.md`](../docs/lean/naming-conventions.md)
> 以下はその上に適用する **S2IL プロジェクト固有のルール** である。

### 命名の長さ方針

このプロジェクトのメインコントリビュータはプログラマであり、数学的な短縮変数名には馴染みがない。
**名称が少々長くても、実態を簡潔にわかりやすく表す名称を優先する。**

| スコープ | 方針 | 例 |
|---|---|---|
| public `def` / `theorem` | 理解しやすさを最優先。多少長くてもよい | `isStructurallyBonded`, `groundedPositions`, `shouldProcessBefore_no_mutual` |
| private `def` / `theorem` | そのスコープ内で理解しやすい程度の長さでよい | `structuralBfs`, `bottom_rotate180` |
| ローカル変数 / `have` | 短くてよい。Lean/Mathlib 標準の 1 文字変数慣習に従う | `s`, `l`, `h`, `n` |

- **短すぎる識別子は非推奨**: public な定義で 1〜2 文字の識別子（`sp`, `fu` 等）は避ける
- **過度な省略は禁止**: 下表の略称は public スコープでは使わない。ローカル変数・テスト用ヘルパーでは略称を使用して良い

| 略称（禁止） | 正式名称（使用する） | 例 |
|---|---|---|
| `spb` | `shouldProcessBefore` | `shouldProcessBefore_no_mutual` |
| `sortFU` | `sortFallingUnits` | `sortFallingUnits_inversion_is_tied` |
| `fU` | `floatingUnits` | `floatingUnits_elem_positions_disjoint` |
| `σ_ic` | `swapIndex` | `swapIndex_invol` |

- アクロニム `BFS` → `Bfs`（例: `GenericBfsInv`）。Lean 4 の `UpperCamelCase` 規約に従う

### 変数名の慣例（S2IL ドメイン固有）

Lean/Mathlib 標準の 1 文字変数慣習（[リファレンス参照](../docs/lean/naming-conventions.md#変数名の慣例lean--mathlib-標準)）に加え、以下のドメイン固有の慣例を使用する。

| 変数 | 用途 |
|---|---|
| `s`, `s1`, `s2` | `Shape` |
| `l`, `l1`, `l2` | `Layer` |
| `q`, `q1`, `q2` | `Quarter` |
| `p`, `p1`, `p2` | `QuarterPos` |
| `c`, `color` | `Color` |
| `config` | `GameConfig`（省略しない） |
| `d` | `Direction` |

### 仮説名のスタイル

`have` / `let` で導入する仮説名には **`h_` + 記述子** を推奨する。

```lean
-- ✅ 推奨: 記述的な仮説名
have h_settled := settled_of_process s
have h_len : l.length ≥ 1 := by ...
have h_mem : q ∈ cluster := by ...

-- ⚠️ 許容: 短い証明ブロック内では番号付きも可
have h1 : ... := by ...
have h2 : ... := by ...
```

### 等変性定理の命名パターン

rotate180 等変性の定理には一貫したサフィックスを使用する。

| パターン | 用途 | 例 |
|---|---|---|
| `func_rotate180` | 関数の rotate180 に関する等式 | `getDir_rotate180`, `eastHalf_rotate180` |
| `func_rotate180_comm` | 関数と rotate180 の可換性 | `cut_rotate180_comm`, `stack_rotate180_comm` |

同じパターンは他の対称操作にも適用する（例: `func_rotateCW`, `func_rotateCCW`）。

### スコープ修飾子の使い分けと WIP フロー

詳細: [`docs/agent/protected-wip-workflow.md`](../docs/agent/protected-wip-workflow.md)

| 修飾子 | 意味 | REPL アクセス |
|---|---|---|
| `private` | ファイル内部専用。証明済み・安定 | ❌ |
| `protected` (意図的) | FQN 半公開。他ファイルから `@Ns.name` で参照される | ✅ FQN 必須 |
| `protected` (WIP) | 証明作業中の一時公開。`-- [WIP]` タグ必須 | ✅ FQN 必須 |
| なし (public) | 外部公開 API | ✅ |

**WIP フローの要点**:
- sorry が残る内部補題・REPL 試行が必要な補題は `protected` + `-- [WIP]` コメントで定義する
- `private` → `protected` 変換時は、同一 namespace 内の呼び出し箇所も FQN に更新する（`protected` は同一 namespace 内でも short name を無効化する）
- 証明チェーン完了・見直し完了後に `-- [WIP]` を削除し `private` に戻す（FQN 呼び出し箇所も short name に戻す）
- `grep_search: query = "-- [WIP]"` でクリーンアップ未了の補題を列挙できる
- クリーンアップ後は `lake build` で `errors = 0` を確認してコミット

### doc コメント規約

| 対象 | 規約 |
|---|---|
| public `def` / `theorem` | **必須**: 日本語の `/-- ... -/` を付与する |
| private `def` / `theorem` | 推奨（義務ではない） |

```lean
-- ✅ 正しい形式
/-- 構造結合により到達可能な全象限を返す -/
def structuralCluster (s : Shape) (pos : QuarterPos) : Finset QuarterPos := ...

/-- placeAbove は rotate180 と可換 -/
theorem placeAbove_rotate180 : ...
```

- 1 行形式を基本とする
- 言語は日本語

### `open` 指令の方針

名前空間全体の `open` は原則禁止。必要な名前のみ選別的にインポートする。

```lean
-- ✅ 選別的インポート
open QuarterPos (getQuarter_rotate180 getQuarter_rotate180_inv)
open Gravity (any_map_rotate180_beq)

-- ❌ 名前空間全体のオープン
open Gravity
```

### 名前空間の設計パターン

- **実装モジュール**（`Gravity`, `PinPusher` 等）: 内部ヘルパー・private 定義を配置
- **公開 API**: `Shape` 名前空間に拡張して定義し、ドット記法で呼び出せるようにする

```lean
-- 実装モジュール
namespace PinPusher
  def liftUp (s : Shape) : Shape := ...
  def generatePins (lifted : Shape) (originalBottom : Layer) : Shape := ...
end PinPusher

-- 公開 API（Shape 名前空間に拡張）
namespace Shape
  def pinPush (s : Shape) (config : GameConfig) : Option Shape := do
    let lifted := PinPusher.liftUp s
    ...
end Shape
```

## Lean 4 証明スタイル

- **裸 `simp` 禁止**: 最終証明では `simp only [...]` を使う。裸 `simp` は Mathlib 更新で壊れうる
  - 探索時: `simp` → 成功したら `simp?` で補題リスト取得 → `simp only [...]` に置換
  - `simp_all` も同様に `simp_all only [...]` を推奨
  - 詳細: `.github/skills/lean-simp-guide/SKILL.md`

## GameConfig（ゲーム設定）の設計方針

詳細: [`docs/s2il/game-config.md`](../docs/s2il/game-config.md)

- `GameConfig` は構造体。関数には明示的に引数として渡す（型クラス・デフォルト引数は不使用）
- プリセット: `vanilla4`（4層）, `vanilla5`（5層）, `stress8`（8層テスト用）

## 証明作業の持続走行ルール

証明作業（Wave 等）では、**ユーザーが明示的に「終わり」「コミット」「止めて」と言うまで作業を継続する**。
小さなマイルストーン（ビルド成功・補題1件証明等）で自発的に停止しない。

**禁止事項**:
- sorry 数が減少していない段階で「コミットしますか?」と提案すること
- ビルド成功のたびにユーザーに次のアクションを確認すること
- 「ここで一旦区切りましょう」等の中断提案
- 「再構成完了」「準備完了」等の中間マイルストーンで停止すること（sorry 数が不変でも次の sorry 証明を即座に開始する）

**作業継続フロー**:
1. ビルド成功 → 実行計画（`gravity-proof-execution-plan.md`）の推奨作業順序を参照
2. 次の未完了タスクに自動的に着手
3. コンテキスト圧縮が発生したら → セッションメモリに保存し、**作業を継続**（停止しない）
4. 行き詰まった場合 → 別のアプローチを試行するか、次のタスクに切り替える

**コミットのタイミング**:
- sorry 数が実際に減少した時（自動コミット可）
- ユーザーが明示的にコミットを要求した時
- セッション終了時（ユーザーの終了宣言後）

**REPL 証明済み補題の当日コミット原則**: REPL でゴールを閉じた補題は、**そのセッション内**でファイルへの追加・フルビルド確認・コミットまで完了する。次セッションに持ち越すと「REPL-verified but not committed」が蓄積し、次セッション開始時の sorry 状態把握が困難になる。

## 新規ヘルパー追加前の重複チェック

3,000 行超のファイル（Gravity/SettleFoldlEq.lean 等）にヘルパー補題を追加する場合、**必ず事前に重複チェック**を行うこと。

1. `grep_search` で関数名・キーワード（例: `foldl_min`, `minLayer`, `mem_of_any`）を検索
2. `s2il-lemma-index.md` のユーティリティ補題セクションを確認
3. 重複がないことを確認してから追加。既存ヘルパーで代替可能な場合はそちらを使う

## Wave 開始時の Explore バッチ取得フロー

3,000 行超のファイル（Gravity/SettleFoldlEq.lean 等）で証明作業を開始する場合、最初に Explore サブエージェントで対象の全定理シグネチャ + 行番号をバッチ取得し、セッションメモリに記録する。

1. Explore に「対象の定理名リスト + 必要な情報（開始行・終端行・シグネチャ）」を指定
2. 結果をセッションメモリ (`/memories/session/`) にテーブル形式で記録
3. 以降のメイン会話では `read_file` でピンポイント読み（行番号が既知のため効率的）

## 証明戦略の検討上限（Proof-First-Test 原則）

**sorry に着手する前の必須ステップ 0（証明計画より先に実施）**:
 sorry の補題シグネチャが確定したら、**コード読解・アプローチ検討を始める前に** `lean-theorem-checker` エージェントまたは REPL `#eval` で補題の真偽を確認する。
- 「任意の obs で成り立つか」を具体値 1-2 個で確認（~5 分）
- 偽と判明したら補題のシグネチャ修正を先行する。証明アプローチの検討は偽補題が修正されてから開始する
- **このステップを省略してインライン推論に入ることは禁止**

**sorry が `∀ obs` 形式で偽と判明した直後の必須ステップ 0.5**:
 sorry の**呼び出し元**（sorry を使っている帰納補題のシグネチャ）を `read_file` または `grep_search` で即座に確認する。
- 呼び出し元が `h_step : ∀ obs', ...` を要求している場合 → 「sorry に条件 I を追加して証明する」路線は **DEAD END**。条件候補の列挙・検証に入ることを禁止する
- 代わりに「呼び出し元の帰納スキームを stronger variant に差し替えられるか」を先に検討する
- **背景**: `foldl_grounded_induction` の `∀ obs'` 要求を見落とし、15+ 不変量候補を逐次検証・棄却した事例がある。呼び出し元確認は ~1 分で完了する

新しい証明アプローチを検討する場合、**インライン推論のみで 3 アプローチ以上を検討することは禁止**。
3 つ目で行き詰まったら、必ず計算的検証（REPL / Scratch `#eval`）を挟んで判断する。

| ステップ | 内容 | 上限 |
|---|---|---|
| 1. アプローチの前提特定 | 証明が依拠する数学的性質を特定（例: 「全ペア可換性」） | — |
| 2. 計算的検証 | REPL / Scratch でその性質の真偽を具体例で計算検証（~1 分） | — |
| 3. 判断 | 偽なら即座にアプローチを棄却、真なら推論を展開 | — |

- **計算的不変量チェックは 2 スケールで打ち切る**: 「最小スケール（violations=0 確認）+ 最大困難ケース（既知の境界例 or 反例候補）」の 2 ステップで判断する。中間スケールの追加は禁止（同方向の数学的新情報が追加されない場合）。
- **禁止**: ツール呼び出しなしで 500 文字以上のアプローチ検討テキストを出力すること
- **反例検出時の即時撤退**: 計算テストでアプローチの前提条件が偽と判明したら、そのアプローチは即座に棄却する。「特殊条件下で成り立つかもしれない」という追加推論は行わない

> **背景**: インライン推論のみで 8 アプローチを逐次検討・棄却した結果、コンテキスト圧縮 2 回 + ~30K トークンを浪費した事例がある。計算テストは ~1 分で決着がつく。

## コード変更前の REPL 即時検証（推奨）

**行数に関わらず、以下の変更を行う前に REPL で即時検証すること。**
ビルドサイクル（各数分）の無駄打ちを防ぐ。

| 変更の種類 | REPL 検証方法 | 目的 |
|---|---|---|
| タクティク変更（`subst` → `rw` 等） | sorry ゴールを REPL で再現し新タクティクを試行 | 破壊的タクティクの副作用を事前検出 |
| Mathlib API 名の使用 | `#check @Finset.sort_toFinset` 等 | 定数の存在確認（1行で完了） |
| `have` / `suffices` の型変更 | sorry ゴール内で型推論を検証 | 型ミスマッチの早期発見 |
| `simp` lemma リストの変更 | `simp only [...]` を REPL で試行 | 補題の適用可能性確認 |
| Bool 否定変換（`¬(b = false)` → `b = true` 等） | `#check @Bool.not_eq_false`, `#check @Bool.eq_false_iff` 等 | Bool 補題の返り値型確認（型ミスで 1-2 ビルド失敗を防ぐ） |

**ビルドを REPL の代わりに使わない**: REPL（~15s）はビルド（~数分）の 10 倍以上高速。

## 大量コード挿入前の REPL 段階検証（必須）

**200 行以上のコードを既存ファイルに一括挿入する場合、REPL で主要な補題を事前検証すること。**
フルビルドの反復（各数分）を避け、エラーの早期発見に努める。

| ステップ | 内容 | 目的 |
|---|---|---|
| 1. 基盤補題 | 型定義・基本等式を REPL で検証 | 名前空間・import 解決 |
| 2. 中核補題 | パイプライン等変性・帰納法ステップ | motive 推論・タクティク動作確認 |
| 3. 一括挿入 | 検証済みコードをファイルに挿入 | — |
| 4. フルビルド | `lake build` で全体整合性確認 | 1〜2 回で通す |

- **private 定義を REPL で検証する場合**: `namespace Gravity ... end Gravity` で囲むか、`Scratch/*.lean` + `open Gravity` を使う
- 特にリスクが高い箇所: 名前空間解決（`open` 文）、`induction` の motive 推論、`simp` のゴール全消し

**ステップ 2 で必ず検証すべき共通パターン**:

| パターン | REPL 検証方法 | リスク |
|---|---|---|
| `push_neg` / `push Not` の分解形 | REPL でゴールを再現し `push_neg` の出力を確認 | `¬∃ q, P ∧ Q` → curried `P → ¬Q`（`¬(P ∧ Q)` でない）|
| `rw [h]` / `rw [← h]` の方向 | sorry ゴールで実際に試行 | 方向逆のまま挿入で確実にエラー |
| Bool/Prop 変換（`isEmpty = false` 等） | `#check @Bool.eq_false_iff_ne_true` 等で利用可能な補題を確認 | `isEmpty = false` と `(!decide (isEmpty = true)) = true` は型が異なる |
| `simp only [...]` のゴール全消し | REPL でリストを適用して確認 | 不十分なリストはゴール残存のまま通過 |
| `push_neg` の使用（非推奨） | `push Not` への置換後に REPL で動作確認 | Mathlib でリネーム済み。`push_neg` 使用でビルド警告が出る |
| `simp` の `injEq` 補題欠落（コンストラクタ等式） | `#check List.cons.injEq` / `#check Prod.mk.injEq` 等で必要補題を確認 | `⟨a, b⟩ = ⟨c, d⟩` ゴールで `injEq` がないと `simp only` が止まる |

## Mathlib 補題探索の推奨フロー

Mathlib / Batteries の補題名・API 名を特定する場合、以下のエスカレーションフローに従う。

1. **REPL `#check @候補名`**（~15s）: 候補名が判明している場合、最初に存在確認 + 型シグネチャ検証。3 候補以内で見つからなければ次へ
2. **`lean-mathlib-search` スキル発動**: `#loogle` / `exact?` / `apply?` 等で体系的に検索
3. **Explore**: `.lake/packages/mathlib/` 配下のソースファイルを `grep_search` で検索
4. **Build**: 全体整合性の最終確認

**禁止**: ステップ 1-2 をスキップして直接 `Select-String` / `Get-ChildItem` でパッケージディレクトリを走査すること。ターミナルでの直接パッケージ走査は最終手段（ステップ 3 で見つからない場合のみ）。

## 一時ファイル・実験作業

`Scratch/` ディレクトリは実験・検証用の一時ファイル置き場。JSONL 生成方法・ファイル命名・`.repl/` との役割分担は [`Scratch/AGENTS.md`](../Scratch/AGENTS.md) を参照。

- **トップレベルへの一時ファイル作成は禁止**（`check_*.lean`・`tmp_*.lean` 等）
- 型チェック / `#eval`: `lake env lean Scratch/MyFile.lean`
- `def main` 実行: `lake env lean --run Scratch/MyFile.lean`（**`--run` はファイル名より前**）

## Lean REPL

`lake exe repl` による対話的 Lean 評価が利用可能（`leanprover-community/repl` 導入済み）。
フルビルドなしで `#eval`・タクティク・sorry ゴール確認が行える。

使用方法の詳細は `lean-repl` スキル（`.github/skills/lean-repl/SKILL.md`）および
[REPL ガイド](../.github/skills/lean-repl/references/repl-guide.md) を参照。
