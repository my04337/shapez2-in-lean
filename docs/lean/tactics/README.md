# タクティク文書体系 — 設計ガイド

> サブエージェントがタクティク情報を検索・選択・利用するための設計仕様書。

> **免責事項**: 本資料は Mathlib v4.29.0（`c6cdc1bb`）時点の情報に基づく。Lean/Mathlib のバージョンアップによりタクティク名・挙動・利用可否が変わる場合がある。Pros/Cons やゴールパターンなど確認が困難な項目は空欄または「情報不十分」として記載している。内容の正確性は保証しない。

---

## ディレクトリ構成

```
docs/lean/tactics/
├── README.md                            — この設計ガイド
├── TEMPLATE.md                          — 詳細ページの標準テンプレート・記法規則
├── QUALITY.md                           — 品質チェック基準
├── index.md                             — 全タクティク索引（300+ エントリ）
├── official/                            — 公式ドキュメント HTML（ローカルキャッシュ）
│   ├── mathlib4-v4.29.0.html            — Mathlib4 タクティク一覧
│   └── lean4ref-v4.29.0.html            — Lean4 公式リファレンス タクティク章
└── detail/                              — タクティク詳細ページ群（カテゴリ別サブディレクトリ）
    ├── 閉鎖/                            — ゴールを完全に閉じるタクティク
    ├── 簡約/                            — 簡約・展開系
    ├── 書換/                            — 等式書き換え系
    ├── 分解/                            — ケース分割・帰納法
    ├── 導入/                            — 変数・仮定の導入
    ├── 補題適用/                        — 補題・定義の適用
    ├── 算術/                            — 算術決定手続き
    ├── 代数/                            — 環・体の等式
    ├── 変換/                            — ゴール形状の変換
    ├── 自動化/                          — 完全自動証明探索
    ├── 探索/                            — 補題検索・提案
    ├── 制御/                            — 実行フロー制御
    ├── 鋳型/                            — 型キャスト正規化
    ├── デバッグ/                        — デバッグ・状態確認
    └── 特化/                            — 特定ドメイン専用
```

---

## エージェント向け利用フロー

```
証明中の問題を特定
│
├─ 「どのタクティクが使えるか分からない」
│   → index.md の カテゴリ列・ゴールパターン列 で候補を絞る
│   → Pros/Cons で比較して選択
│
├─ 「候補はある。使い方・オプションを確認したい」
│   → detail/<カテゴリ>/TACTIC.md を参照（構文・コードサンプル・オプション）
│
├─ 「詳細ページがまだない」
│   → index.md の概要 + official/*.html から確認
│
└─ 「タクティクを使ったら "unknown tactic" エラーになった」
    → 下記「インポート解決フロー」を参照
```

---

## インポート解決フロー

S2IL は Mathlib を**選択的インポート**しているため、組み込みタクティク以外は対応する
`import` 文をファイル先頭に追加しないと "unknown tactic" エラーになる。

```
"unknown tactic '<NAME>'" が出た
│
├─ index.md の 定義元 列を確認
│   ├─ `Lean.Parser.Tactic.*` / `Init.*`
│   │   → Lean 組み込み。追加インポート不要。spell miss や import 内不足を確認。
│   │
│   └─ `Mathlib.*` または `Aesop.*`
│       → 下表の「インポート文」を対象 .lean ファイルの先頭に追加する
│
├─ S2IL 証明ファイルに追加する場合
│   → 当該 .lean ファイルの他の import 行の直後に追記
│
└─ REPL (pickle 環境) で使いたい場合
    → pickle は S2IL インポート済み環境のみ。Mathlib タクティクは追加インポートできない。
      代替タクティク（omega / exact? 等）を使うか、-NoPickle で直接 import する。
```

### タクティク別インポート早見表

| タクティク | 定義元プレフィックス | 追加インポート文 |
|---|---|---|
| `ring`, `ring_nf` | `Mathlib.Tactic.Ring` | `import Mathlib.Tactic.Ring` |
| `linarith`, `nlinarith` | `Mathlib.Tactic.Linarith` | `import Mathlib.Tactic.Linarith` |
| `norm_num` | `Mathlib.Tactic.NormNum` | `import Mathlib.Tactic.NormNum` |
| `positivity` | `Mathlib.Tactic.Positivity` | `import Mathlib.Tactic.Positivity` |
| `field_simp` | `Mathlib.Tactic.FieldSimp` | `import Mathlib.Tactic.FieldSimp` |
| `linear_combination` | `Mathlib.Tactic.LinearCombination` | `import Mathlib.Tactic.LinearCombination` |
| `polyrith` | `Mathlib.Tactic.Polyrith` | `import Mathlib.Tactic.Polyrith` |
| `norm_cast`, `push_cast`, `exact_mod_cast` | `Mathlib.Tactic.NormCast` | `import Mathlib.Tactic.NormCast` |
| `push_neg` | `Mathlib.Tactic.PushNeg` | `import Mathlib.Tactic.PushNeg` |
| `gcongr` | `Mathlib.Tactic.GCongr` | `import Mathlib.Tactic.GCongr` |
| `aesop` | `Aesop` | `import Aesop` |
| `duper` | `Duper` | `import Duper` |
| `tauto` | `Mathlib.Tactic.Tauto` | `import Mathlib.Tactic.Tauto` |
| `itauto` | `Mathlib.Tactic.ITauto` | `import Mathlib.Tactic.ITauto` |
| `congr!` | `Mathlib.Tactic.CongrExclamation` | `import Mathlib.Tactic.CongrExclamation` |
| `convert` | `Mathlib.Tactic.Convert` | `import Mathlib.Tactic.Convert` |
| `choose` | `Mathlib.Tactic.Choose` | `import Mathlib.Tactic.Choose` |
| `lift` | `Mathlib.Tactic.Lift` | `import Mathlib.Tactic.Lift` |
| `abel` | `Mathlib.Tactic.Abel` | `import Mathlib.Tactic.Abel` |
| `group` | `Mathlib.Tactic.Group` | `import Mathlib.Tactic.Group` |
| `module` | `Mathlib.Tactic.Module` | `import Mathlib.Tactic.Module` |
| `bound` | `Mathlib.Tactic.Bound` | `import Mathlib.Tactic.Bound` |
| `fun_prop` | `Mathlib.Tactic.FunProp` | `import Mathlib.Tactic.FunProp` |
| `continuity` | `Mathlib.Tactic.Continuity` | `import Mathlib.Tactic.Continuity` |
| `measurability` | `Mathlib.Tactic.Measurability` | `import Mathlib.Tactic.Measurability` |
| `order` | `Mathlib.Tactic.Order` | `import Mathlib.Tactic.Order` |

**追加インポート不要**（Lean / Init 組み込み）: `simp`, `omega`, `rfl`, `exact`, `apply`, `refine`, `cases`, `induction`, `intro`, `intros`, `rcases`, `obtain`, `use`, `constructor`, `ext`, `funext`, `decide`, `native_decide`, `norm_cast`（Init 版）, `rw`, `calc`, `contradiction`, `assumption`, `grind`, `lia`

---

## index.md の列構成

| 列 | 型 | 説明 |
|---|---|---|
| `名称` | タクティク名（`backtick` 付き） | 主要な検索キー |
| `カテゴリ` | カテゴリタグ | タスク種別での検索 |
| `定義元` | 識別子文字列 | import 先・出典確認用。`Mathlib.*` で始まる場合は上記「インポート早見表」で追加インポートが必要 |
| `ゴールパターン` | パターン記法 | ゴール形状からタクティクへの索引 |
| `概要` | 1–2 行テキスト | 何をするタクティクか |
| `Pros` | 短テキスト | 使うべき条件 |
| `Cons` | 短テキスト | 避けるべき条件・失敗ケース |

---

## カテゴリタグ一覧

単一の短い日本語単語。index.md では 1 エントリに 1 タグを割り当てる（主目的に基づく）。

| タグ | 意味 | 代表タクティク |
|---|---|---|
| `閉鎖` | ゴールを完全に閉じる | `exact`, `rfl`, `trivial`, `decide`, `omega`, `ring`, `norm_num`, `contradiction`, `assumption` |
| `簡約` | ゴール・仮定を簡約/展開する | `simp`, `dsimp`, `simp_all`, `simpa`, `unfold`, `delta`, `norm_cast` |
| `書換` | 等式で書き換える | `rw`, `rewrite`, `erw`, `conv`, `simp only` |
| `分解` | 仮定・帰納型をケース分割 | `cases`, `rcases`, `obtain`, `induction` |
| `導入` | 変数・仮定をコンテキストに導入 | `intro`, `intros`, `rintro`, `ext`, `funext` |
| `補題適用` | 補題・定義・仮定を適用 | `apply`, `refine`, `have`, `specialize`, `replace` |
| `算術` | 線形・非線形算術の決定手続き | `omega`, `linarith`, `nlinarith`, `norm_num`, `positivity` |
| `代数` | 環・体の等式 | `ring`, `ring_nf`, `field_simp`, `linear_combination` |
| `変換` | ゴール形状の変換 | `change`, `generalize`, `suffices`, `exfalso`, `by_contra`, `show` |
| `自動化` | 完全自動証明探索 | `aesop`, `grind`, `tauto`, `decide`, `native_decide` |
| `探索` | 使える補題を検索・提案 | `exact?`, `apply?`, `rw?`, `simp?`, `#suggestions` |
| `制御` | 実行フロー制御 | `try`, `first`, `all_goals`, `repeat`, `<;>`, `focus`, `solve` |
| `鋳型` | 型キャスト正規化 | `norm_cast`, `push_cast`, `pull_cast`, `exact_mod_cast` |
| `デバッグ` | デバッグ・状態確認専用 | `sorry`, `trace`, `trace_state`, `guard_hyp`, `done` |
| `特化` | 特定ドメイン専用 | `bv_decide`, `mvcgen`, `Finset.decide`, `polyrith` |

---

## ゴールパターン記法

index.md の `ゴールパターン` 列で使用する短縮記法。複数条件は `/` で区切る。

| 記法 | 適用するゴール形状 | 典型タクティク |
|---|---|---|
| `任意` | どのゴールにも適用可能 | `simp`, `aesop`, `trivial` |
| `等式` | `⊢ a = b` （任意の型） | `rfl`, `ring`, `simp` |
| `線形算術` | Nat/Int の線形不等式・等式 | `omega`, `linarith` |
| `非線形算術` | 非線形な算術式 | `nlinarith`, `polyrith` |
| `環式` | 環 (CommSemiring等) 上の等式 | `ring`, `ring_nf`, `grind` |
| `∀/→` | `⊢ ∀ x, P x` または `⊢ A → B` | `intro`, `intros`, `rintro` |
| `∃` | `⊢ ∃ x, P x` | `use`, `exists`, `refine ⟨_, _⟩` |
| `∧` | `⊢ A ∧ B` | `constructor`, `and_intros`, `exact ⟨_, _⟩` |
| `∨` | `⊢ A ∨ B` | `left`, `right`, `rcases` |
| `帰納型` | 帰納型コンストラクタに関するゴール | `cases`, `induction`, `rcases` |
| `仮定依存` | 仮定の形に応じて適用（goal は任意） | `assumption`, `exact`, `apply`, `specialize` |
| `False` | `⊢ False` または矛盾する仮定がある | `contradiction`, `exfalso`, `omega` |
| `Decidable` | `Decidable P` が成立する命題 | `decide`, `native_decide` |
| `キャスト` | 型キャスト `↑` / `↓` を含む式 | `norm_cast`, `push_cast` |
| `関数等式` | `⊢ f = g`（関数の外延的等価） | `funext`, `ext` |
| `変換後` | ゴール形状変換のみ行い自分では閉じない | `change`, `generalize`, `suffices`, `show` |

---

## エージェント向けタクティク選択フロー

### Step 1: ゴールを分類する

```
⊢ P の形を確認
│
├─ P が等式 a = b
│   ├─ a, b が Nat/Int の線形式 → omega
│   ├─ a, b が環上の式 (+, *, ^) → ring
│   ├─ 定義展開すれば自明 → rfl / decide
│   ├─ simp 補題で成立 → simp [lemmas] または simp only [lemmas]
│   └─ 複雑な等式証明 → calc + 個別補題
│
├─ P が不等式または算術
│   ├─ 線形 Nat/Int → omega
│   ├─ 線形 Real/ℚ → linarith
│   ├─ 非線形 → nlinarith + ヒント，または polyrith
│   └─ 具体的な数値計算 → norm_num
│
├─ P が ∀ x, ... または A → B
│   └─ intro / intros / rintro で仮定を導入してから再分類
│
├─ P が ∃ x, ...
│   └─ use 具体値 → 残ゴールを証明
│
├─ P が A ∧ B
│   └─ constructor → 各ゴールを個別に証明
│
├─ P が A ∨ B
│   └─ left（A を証明） or right（B を証明）
│
├─ 矛盾（仮定に h : P と h' : ¬P など）
│   └─ contradiction / omega / simp_all
│
└─ 上記以外（複雑・不明）
    → 1. exact? で候補を探す
      2. aesop で自動化を試みる
      3. grind で SMT 的推論を試みる
      4. sorry で一時スキップして証明骨格を確立してから戻る
```

### Step 2: 仮定の分解が必要な場合

```
仮定 h の型 T に応じて:
│
├─ T は A ∧ B → rcases h with ⟨ha, hb⟩ または obtain ⟨ha, hb⟩ := h
├─ T は A ∨ B → rcases h with ha | hb
├─ T は ∃ x, ... → obtain ⟨x, hx⟩ := h
├─ T は 帰納型 → cases h または rcases h with | con₁ => ... | con₂ => ...
└─ T の値でケース分け → cases h（帰納命題）or omega（数値条件）
```

### Step 3: タクティクが失敗したとき

```
タクティクが失敗 / 期待通りに動かない
│
├─ simp が遅い / ループ → simp? で simp only 化
├─ omega が失敗 → 実数・体が混在していないか確認（linarith に切替）
├─ ring が失敗 → field_simp してから ring
├─ apply が失敗 → 型を exact? で確認，unification 問題なら refine + _
├─ exact が失敗 → apply + assumption で分割
└─ 全部失敗 → grind / aesop で試し，sorry でスキップして後回し
```

---

## 詳細ページ優先作成リスト

### 優先度 A（最頻使用・複雑）

`simp` / `simp only`, `omega`, `ring` / `ring_nf`, `rcases` / `obtain`, `apply` / `exact` / `refine`, `linarith` / `nlinarith`

### 優先度 B（中頻度・中複雑）

`rw` / `rewrite`, `norm_num`, `aesop` / `grind`, `cases` / `induction`, `norm_cast` / `push_cast`, `field_simp`, `positivity`

### 優先度 C（低頻度・特化）

`linear_combination`, `polyrith`, `decide`, `native_decide`, `bv_decide`, `conv`, `ext`, `funext`, `tauto`, `exact?`, `apply?`, `simp?`

---

## 更新・メンテナンスガイド

- テンプレート仕様 → `TEMPLATE.md`
- 品質チェック基準 → `QUALITY.md`
- Lean/Mathlib バージョンアップ後: index.md の概要・Cons を更新し、バージョン注記を追記

---

## 出典・ライセンス

| ソース | URL | ライセンス |
|---|---|---|
| Lean 4 公式リファレンス | https://lean-lang.org/doc/reference/latest/ | Apache-2.0 (© Lean FRO) |
| Mathlib4 ドキュメント | https://leanprover-community.github.io/mathlib4_docs/ | Apache-2.0 (© Mathlib Contributors) |
| seasawher/mathlib4-help | https://seasawher.github.io/mathlib4-help/ | 記載なし（参照元として利用） |

本ドキュメント自体は MIT License で提供される。
