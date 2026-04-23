# Lean 4 / Mathlib タクティク索引 v2

Mathlib バージョン: `c6cdc1bb118778092f976bf4598bc63349b6d3c7`（v4.29.0 相当）

参照元:
- `docs/lean/tactics/official/mathlib4-v4.29.0.html` — Mathlib4 タクティク一覧
- `docs/lean/tactics/official/lean4ref-v4.29.0.html` — Lean 4 公式リファレンス タクティク章

> **免責事項**: 本索引は上記バージョン時点の情報に基づく。Lean/Mathlib のバージョンアップにより内容が古くなる場合がある。Pros/Cons やゴールパターンなど確認が困難な項目は空欄または「情報不十分」として記載している。内容の正確性は保証しない。

---

## 凡例

| 列 | 説明 |
|---|---|
| 名称 | タクティクのシンタックス名（詳細ページがある場合はリンク付き） |
| カテゴリ | 分類タグ（閉鎖/簡約/書換/分解/導入/補題適用/算術/代数/変換/自動化/探索/制御/鋳型/デバッグ/特化） |
| 定義元 | 公式ドキュメントに記載された識別子 |
| ゴールパターン | 適用可能なゴール形状（任意/等式/線形算術/非線形算術/環式/∀→/∃/∧/∨/帰納型/仮定依存/False/Decidable/キャスト/関数等式/変換後） |
| 概要 | 1〜2行の簡潔な説明 |
| Pros | 効果的な場面 |
| Cons | 避けるべき場面・注意点 |

---

## 優先度 A — 最頻使用・高複雑度

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `simp` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.simp` | 任意 | `@[simp]` 補題で繰り返し書き換えて簡約 | 汎用簡約・巨大な補題DB | 非終端利用は脆弱・遅い場合あり |
| `simp only` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.simp` | 任意 | 指定補題のみで簡約（安定版） | 再現性が高い・最終証明向き | 補題リストの手動管理 |
| `omega` [→詳細](detail/算術/omega.md) | 算術 | `Lean.Parser.Tactic.omega` | 線形算術 | Nat/Int 線形算術の決定手続き | 線形算術を完全決定 | 非線形・Real 不可 |
| `ring` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring` | 環式 | 可換環の等式を正規化して証明 | 環の等式を確実に決定 | 不等式不可・仮定不使用 |
| `ring_nf` [→詳細](detail/代数/ring_nf.md) | 代数 | `Mathlib.Tactic.Ring.ringNF` | 環式 | 環式を正規形に変換（閉じない） | 正規化のみ・準備ステップ | ゴールを閉じない |
| `rcases` [→詳細](detail/分解/rcases.md) | 分解 | `Lean.Parser.Tactic.rcases` | 帰納型/∧/∨/∃ | パターン指定で再帰的に分解 | 深いネスト分解を1行で | パターン構文が複雑 |
| `obtain` [→詳細](detail/分解/obtain.md) | 分解 | `Lean.Parser.Tactic.obtain` | ∧/∃/帰納型 | `have` + `rcases` の糖衣構文 | 導入と分解を1行で | 型注釈を伴う場合限定 |
| `apply` [→詳細](detail/補題適用/apply.md) | 補題適用 | `Lean.Parser.Tactic.apply` | 仮定依存 | 結論をゴールにマッチさせ前提をサブゴールに | 逆方向推論の基本 | 型マッチ失敗あり |
| `exact` [→詳細](detail/閉鎖/exact.md) | 閉鎖 | `Lean.Parser.Tactic.exact` | 仮定依存 | 指定した項でゴールを正確に閉じる | ゴールを一撃で閉じる | 完全一致が必要 |
| `refine` [→詳細](detail/補題適用/refine.md) | 補題適用 | `Lean.Parser.Tactic.refine` | 仮定依存 | `?_` プレースホルダーでサブゴールを残す | 部分項+サブゴール生成 | `?_` の位置指定が紛らわしい |
| `linarith` [→詳細](detail/算術/linarith.md) | 算術 | `Mathlib.Tactic.Linarith.linarith` | 線形算術 | 線形算術の不等式を Farkas 補題で解く | Real/ℚ の線形不等式に対応 | Nat → omega の方が速い |
| `nlinarith` [→詳細](detail/算術/nlinarith.md) | 算術 | `Mathlib.Tactic.Polyrith.nlinarith` | 非線形算術 | `linarith` の非線形拡張 | 非線形不等式に対応 | ヒント必要な場合あり |

---

## 優先度 B — 中頻度・中複雑度

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `rw` [→詳細](detail/書換/rw.md) | 書換 | `Lean.Parser.Tactic.rwSeq` | 等式 | 等式規則で書き換え + `rfl` 即時クローズ | 位置明確な書換 | 最初の出現のみ |
| `norm_num` [→詳細](detail/算術/norm_num.md) | 算術 | `Mathlib.Tactic.normNum` | 等式/線形算術 | 数値計算を正規化して証明 | 数値計算を確実に証明 | 変数含む式は不可 |
| `aesop` [→詳細](detail/自動化/aesop.md) | 自動化 | `Aesop.Frontend.Parser.aesopTactic` | 任意 | ルールベース自動証明探索 | ルールベース汎用探索 | 遅い・ルール不足で失敗 |
| `grind` [→詳細](detail/自動化/grind.md) | 自動化 | `Lean.Parser.Tactic.grind` | 任意 | SMT ソルバー風の汎用証明 | SMTベースの強力自動化 | 新しく変更可能性あり |
| `cases` [→詳細](detail/分解/cases.md) | 分解 | `Lean.Parser.Tactic.cases` | 帰納型 | 帰納型のケース分析 | 基本のケース分析 | 1段ずつのみ |
| `induction` [→詳細](detail/分解/induction.md) | 分解 | `Lean.Parser.Tactic.induction` | 帰納型 | 帰納法の仮説を自動生成 | 帰納法の標準タクティク | 一般化が必要な場合あり |
| `norm_cast` [→詳細](detail/鋳型/norm_cast.md) | 鋳型 | `Lean.Parser.Tactic.tacticNorm_cast_` | キャスト | キャストを正規化 | キャストを自動正規化 | 補題不足で不完全な場合 |
| `push_cast` [→詳細](detail/鋳型/push_cast.md) | 鋳型 | `Lean.Parser.Tactic.tacticPush_cast_` | キャスト | キャストを式の内側に押し込む | キャストを葉に向けて押す | 方向が逆の場合は pull_cast |
| `field_simp` [→詳細](detail/代数/field_simp.md) | 代数 | `Mathlib.Tactic.fieldSimp` | 環式 | 体の分母をキャンセルして簡約 | 体の分母を自動消去 | Field 以外不可 |
| `positivity` [→詳細](detail/算術/positivity.md) | 算術 | `Mathlib.Tactic.Positivity.positivity` | 等式/線形算術 | `0 ≤ x` / `0 < x` を構造的に証明 | 0≤/0< を構造的に解決 | 0≤/0< の形のみ |
| `conv` [→詳細](detail/書換/conv.md) | 書換 | `Lean.Parser.Tactic.Conv.conv` | 任意 | 部分式にフォーカスして書き換え | 精密な位置指定書換 | 学習コスト高い |

---

## 優先度 C — 特化・低頻度

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `linear_combination` [→詳細](detail/代数/linear_combination.md) | 代数 | `Mathlib.Tactic.LinearCombination.linearCombination` | 等式 | 仮定の線形結合で等式証明 | 仮定の線形結合で等式証明 | 係数を自分で指定 |
| `polyrith` [→詳細](detail/代数/polyrith.md) | 代数 | `Mathlib.Tactic.Polyrith.polyrith` | 環式/非線形算術 | 外部 CAS で多項式算術を証明 | 自動係数発見 | 外部 CAS が必要 |
| `decide` [→詳細](detail/自動化/decide.md) | 自動化 | `Lean.Parser.Tactic.decide` | Decidable | Decidable 命題を評価して証明 | Decidable 命題を完全決定 | 大規模で遅い |
| `native_decide` [→詳細](detail/自動化/native_decide.md) | 自動化 | `Lean.Parser.Tactic.nativeDecide` | Decidable | `decide` のコンパイラ使用版 | 高速な decide | コンパイラ信頼が必要 |
| `bv_decide` [→詳細](detail/特化/bv_decide.md) | 特化 | `Lean.Parser.Tactic.bvDecide` | Decidable | SAT でビットベクトル命題を決定 | BitVec の SAT 決定 | BitVec 以外不可 |
| `ext` [→詳細](detail/導入/ext.md) | 導入 | `Lean.Elab.Tactic.Ext.ext` | 関数等式 | `@[ext]` 外延性補題を適用 | 外延性で等式分解 | @[ext] 補題が必要 |
| `funext` [→詳細](detail/導入/funext.md) | 導入 | `Mathlib.Tactic.funextStx` | 関数等式 | 関数外延性 | 関数等式の定番 | dependent fun に注意 |
| `tauto` [→詳細](detail/自動化/tauto.md) | 自動化 | `Mathlib.Tactic.Tauto.tauto` | 任意 | 命題論理を自動証明 | 命題論理を自動証明 | 述語論理は限定的 |
| `exact?` [→詳細](detail/探索/exact_question.md) | 探索 | `Lean.Parser.Tactic.exact?` | 任意 | 補題のライブラリ検索 | 補題のライブラリ検索 | 遅い（全探索） |
| `apply?` [→詳細](detail/探索/apply_question.md) | 探索 | `Lean.Parser.Tactic.apply?` | 任意 | apply 用の補題を検索 | apply 補題の自動探索 | 遅い（全探索） |
| `rw?` [→詳細](detail/探索/rw_question.md) | 探索 | `Lean.Parser.Tactic.rwTrace` | 等式 | 書換規則をライブラリ検索 | 書換規則をライブラリ検索 | 遅い（全探索） |
| `simp?` [→詳細](detail/探索/simp_question.md) | 探索 | `Lean.Parser.Tactic.simpTrace` | 任意 | `simp only` の安定版を生成 | simp only の安定版生成 | 探索用（最終証明では置換） |

---

## 基本タクティク — 日常的に使用する標準ツール

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `intro` [→詳細](detail/導入/intro.md) | 導入 | `Lean.Parser.Tactic.intro` | ∀/→ | ゴールの前件・全称量化子を導入 | ∀/→ 分解の基本 | 名前衝突に注意 |
| `intros` [→詳細](detail/導入/intros.md) | 導入 | `Lean.Parser.Tactic.intros` | ∀/→ | `intro` の複数回版 | 一度に全部導入 | 名前の自動割当 |
| `rintro` [→詳細](detail/導入/rintro.md) | 導入 | `Lean.Parser.Tactic.rintro` | ∀/→ | `intro` + `rcases` の統合版 | 導入と分解を同時に | パターン構文が複雑 |
| `constructor` [→詳細](detail/導入/constructor.md) | 導入 | `Lean.Parser.Tactic.constructor` | ∧/∃ | 最初のコンストラクタを適用 | And/Exists の定番 | 1つ目のみ |
| `left` [→詳細](detail/導入/left.md) | 導入 | `Lean.Parser.Tactic.left` | ∨ | Or.inl を適用 | 左の選択肢を選ぶ | Or 型限定 |
| `right` [→詳細](detail/導入/right.md) | 導入 | `Lean.Parser.Tactic.right` | ∨ | Or.inr を適用 | 右の選択肢を選ぶ | Or 型限定 |
| `use` [→詳細](detail/導入/use.md) | 導入 | `Mathlib.Tactic.useSyntax` | ∃ | 存在量化子に witness を提供 | 存在証明の定番 | witness の手動指定 |
| `exists` [→詳細](detail/導入/exists.md) | 導入 | `Lean.Parser.Tactic.«tacticExists_,,»` | ∃ | `refine ⟨e, ...⟩; try trivial` の糖衣 | core の存在導入 | trivial で閉じない場合あり |
| `have` [→詳細](detail/補題適用/have.md) | 補題適用 | `Lean.Parser.Tactic.tacticHave_` | 任意 | 不透明な仮定を追加 | 中間結果の導入 | ゴールを閉じない |
| `let` [→詳細](detail/導入/let.md) | 導入 | `Lean.Parser.Tactic.tacticLet_` | 任意 | 展開可能なローカル定義 | 値を保持（have と異なる） | 展開で大きくなる場合 |
| `specialize` [→詳細](detail/補題適用/specialize.md) | 補題適用 | `Lean.Parser.Tactic.specialize` | 仮定依存 | 仮定の全称量化子を例化 | 仮定の具体化 | 元の一般仮定を失う |
| `replace` [→詳細](detail/補題適用/replace.md) | 補題適用 | `Lean.Parser.Tactic.replace` | 任意 | `have` + 同名仮定の削除 | 仮定の上書き更新 | 元の仮定を失う |
| `rfl` [→詳細](detail/閉鎖/rfl.md) | 閉鎖 | `Lean.Parser.Tactic.tacticRfl` | 等式 | 反射律でゴールを閉じる | x = x を一撃で | 定義的等価でないと失敗 |
| `assumption` [→詳細](detail/閉鎖/assumption.md) | 閉鎖 | `Lean.Parser.Tactic.assumption` | 仮定依存 | 互換型の仮定でゴールを閉じる | 仮定から自動選択 | 完全一致が必要 |
| `contradiction` [→詳細](detail/閉鎖/contradiction.md) | 閉鎖 | `Lean.Parser.Tactic.contradiction` | False | 矛盾する仮定からゴールを閉じる | 矛盾の自動検出 | 明示的矛盾が必要 |
| `trivial` [→詳細](detail/閉鎖/trivial.md) | 閉鎖 | `Lean.Parser.Tactic.tacticTrivial` | 任意 | rfl/contradiction/assumption 等を順に試す | 簡単なゴールを自動閉鎖 | 強力ではない |
| `by_cases` [→詳細](detail/分解/by_cases.md) | 分解 | `Classical.«tacticBy_cases_:_»` | 任意 | `p ∨ ¬p` でケース分岐 | 場合分けの定番 | 排中律を使用 |
| `split` [→詳細](detail/分解/split.md) | 分解 | `Lean.Parser.Tactic.split` | Decidable | if/match を分岐 | if/match の展開 | if のみ対象 |
| `change` [→詳細](detail/変換/change.md) | 変換 | `Lean.Parser.Tactic.change` | 変換後 | ゴールを定義的に等しい型に変更 | ゴールの書き直し | 定義的等価が必要 |
| `suffices` [→詳細](detail/変換/suffices.md) | 変換 | `Lean.Parser.Tactic.tacticSuffices_` | 変換後 | 「〜を示せば十分」の形に変換 | 証明の方針提示 | 追加サブゴール発生 |
| `calc` [→詳細](detail/変換/calc.md) | 変換 | `Lean.calcTactic` | 等式/任意 | 推移的関係の段階的推論 | 可読性の高い段階証明 | 各ステップの証明が必要 |
| `symm` [→詳細](detail/変換/symm.md) | 変換 | `Lean.Parser.Tactic.symm` | 等式 | 対称性で等式の向きを反転 | a = b → b = a | @[symm] 必要 |
| `congr` [→詳細](detail/変換/congr.md) | 変換 | `Lean.Parser.Tactic.congr` | 等式 | f a = f b を a = b に分解 | 関数適用の等式分解 | 深い一致が必要な場合 |
| `exfalso` [→詳細](detail/変換/exfalso.md) | 変換 | `Lean.Parser.Tactic.tacticExfalso` | False | ゴールを ⊢ False に変換 | 背理法の開始 | 矛盾の証明が必要 |
| `by_contra` [→詳細](detail/変換/by_contra.md) | 変換 | `Lean.Parser.Tactic.byContra` | False/変換後 | 矛盾による証明 | ¬P 仮定で背理法 | 古典論理を使用 |
| `push_neg` [→詳細](detail/変換/push_neg.md) | 変換 | `Mathlib.Tactic.PushNeg.tacticPush_neg_` | 任意 | 否定を量化子内側に押し込む | ¬∀→∃¬ の自動変換 | 複雑な否定は部分的 |
| `subst` [→詳細](detail/変換/subst.md) | 変換 | `Lean.Parser.Tactic.subst` | 仮定依存 | 等式仮定で変数を置換 | 変数の即座消去 | x = e形式のみ |
| `sorry` [→詳細](detail/デバッグ/sorry.md) | デバッグ | `Lean.Parser.Tactic.tacticSorry` | 任意 | 未完証明のプレースホルダー | 証明骨格の構築 | 本番証明に残さない |
| `dsimp` [→詳細](detail/簡約/dsimp.md) | 簡約 | `Lean.Parser.Tactic.dsimp` | 任意 | 定義的簡約のみ（軽量） | 定義的簡約のみ・軽量 | simp 未満の書換力 |
| `simpa` [→詳細](detail/簡約/simpa.md) | 簡約 | `Lean.Parser.Tactic.simpa` | 任意 | simp + `using e` で仕上げ | simp+仕上げの定番 | using e との相性注意 |
| `simp_all` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.simpAll` | 任意 | 全仮定+ゴールを一括簡約 | 全仮定+ゴールを一括簡約 | 過剰な変化リスク |
| `unfold` [→詳細](detail/簡約/unfold.md) | 簡約 | `Lean.Parser.Tactic.unfold` | 任意 | 定義を1段階展開 | 指定定義のみ展開 | equation lemma 必要 |

---

## 全タクティク一覧（アルファベット順）

優先度 A〜C・基本タクティクに含まれないタクティクを網羅。変種（`!`/`?`/`?!`）も含む。

### # 系（デバッグ・検索補助）

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `#adaptation_note` | デバッグ | `Mathlib.Tactic.AdaptationNote` | 任意 | 将来の変更に対応するための注釈をタクティクブロック内に挿入 | | |
| `#check` | デバッグ | `Mathlib.Tactic.«tactic#check__»` | 任意 | 項 `t` を精緻化して型 `e : ty` の形で表示 | | |
| `#check'` | デバッグ | `Mathlib.Tactic.«tactic#check'__»` | 任意 | `#check` と同様だが implicit 引数を省略表示 | | |
| `#count_heartbeats` | デバッグ | `Mathlib.CountHeartbeats.«tactic#count_heartbeats_»` | 任意 | ハートビート数を計測表示 | | |
| `#count_heartbeats!` | デバッグ | `Mathlib.CountHeartbeats.«tactic#count_heartbeats!_In__»` | 任意 | 繰り返し計測版（範囲・標準偏差表示） | | |
| `#defeq_abuse` | デバッグ | `Mathlib.Tactic.DefEqAbuse.defeqAbuse` | 任意 | 透明度設定変更の検証ツール | | |
| `#find` | 探索 | `Mathlib.Tactic.Find.«tactic#find_»` | 任意 | 結果型がパターンに一致する定義・定理を検索 | | |
| `#leansearch` | 探索 | `LeanSearchClient.leansearch_tactic` | 任意 | Lean Search から補題検索 | | |
| `#loogle` | 探索 | `LeanSearchClient.loogle_tactic` | 任意 | Loogle でライブラリ検索 | | |
| `#search` | 探索 | （複数） | 任意 | ライブラリから関連定理を検索 | | |

---

### 記号・特殊構文

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `(tacs)` | 制御 | `Lean.Parser.Tactic.paren` | 任意 | タクティクのグルーピング | | |
| `·` | 制御 | `Lean.cdot` | 任意 | メインゴールにフォーカスして解く | | |
| `_` | 制御 | `Batteries.Tactic.tactic_` | 任意 | `done` と同様に残りゴールを列挙して失敗 | | |
| `{` / `}` | 制御 | `Lean.Parser.Tactic.nestedTactic` | 任意 | ネストされたタクティクブロック | | |
| `∎` | 探索 | `«tactic∎»` | 任意 | `try?` に展開（`\qed` で入力） | | |
| `<;>` [→詳細](detail/制御/seq_focus.md) | 制御 | `Lean.Parser.Tactic.«tactic_<;>_»` | 任意 | 全サブゴールにタクティクを適用 | 分岐後の共通処理を1行で記述・`cases <;> simp` などのイディオムが頻出 | 全サブゴールで成功が必要・部分成功許容は `<;> try tac` で対応 |

---

### a

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `abel` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel` | 環式 | 加法的可換モノイド・群の等式を解く | 加法的可換モノイド/群の等式をワンショット解決・スカラー倍にも対応 | 乗算含む等式は ring を使うこと・非可換群は group を使うこと |
| `abel!` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel!` | 環式 | `abel` の積極版 | 親ページ（`abel`）と同様 | 親ページ（`abel`）と同様 |
| `abel1` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel1` | 環式 | `abel` の厳格版 | 親ページ（`abel`）と同様 | 親ページ（`abel`）と同様 |
| `abel1!` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel1!` | 環式 | `abel1` の積極版 | 親ページ（`abel`）と同様 | 親ページ（`abel`）と同様 |
| `abel_nf` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel_nf` | 環式 | 群の式を正規形に書き換え | 親ページ（`abel`）と同様 | 親ページ（`abel`）と同様 |
| `abel_nf!` [→詳細](detail/代数/abel.md) | 代数 | `Mathlib.Tactic.Abel.tacticAbel_nf!` | 環式 | `abel_nf` の積極版 | 親ページ（`abel`）と同様 | 親ページ（`abel`）と同様 |
| `absurd` [→詳細](detail/変換/absurd.md) | 変換 | `Batteries.Tactic.tacticAbsurd_` | 仮定依存 | `h : p` からゴールを `⊢ ¬ p` に変換 | ゴールが False でなくても矛盾を利用した証明ができ不可能なケースで直感的 | ¬P を示す手段がない場合閉じられない・h₁/h₂ 両方ある場合は contradiction が簡潔 |
| `ac_change` [→詳細](detail/書換/ac_change.md) | 書換 | `Mathlib.Tactic.acChange` | 等式 | AC 考慮した `change` | 可換演算の項の並び替えを自然に行える・change では通らない並べ替えに対応 | AC 同値性が成り立たない変更には使えない・Mathlib import が必要 |
| `ac_nf` | 書換 | `Mathlib.Tactic.acNF` | 等式 | AC を用いて正規形に書き換え | | |
| `ac_nf0` | 書換 | `Mathlib.Tactic.acNF0` | 等式 | `ac_nf` の内部使用版 | | |
| `ac_rfl` [→詳細](detail/閉鎖/ac_rfl.md) | 閉鎖 | `Mathlib.Tactic.acRfl` | 等式 | AC で等しい式を `rfl` で証明 | 並び替えだけで一致する等式を ring より軽量に閉じられる | AC 以外の等式変換は扱えない・Comm/Assoc インスタンスがない演算では失敗 |
| `admit` | デバッグ | `Lean.Parser.Tactic.tacticAdmit` | 任意 | `sorry` の別名 | | |
| `aesop?` [→詳細](detail/自動化/aesop.md) | 自動化 | `Aesop.Frontend.Parser.aesopTactic?` | 任意 | `aesop` の `Try this` 提案版 | 親ページ（`aesop`）と同様 | 親ページ（`aesop`）と同様 |
| `aesop_cat` | 特化 | （複数） | 任意 | 圏論専用 `aesop` | | |
| `aesop_cat?` | 特化 | （複数） | 任意 | `aesop_cat` の提案版 | | |
| `aesop_cat_nonterminal` | 特化 | `aesop_cat_nonterminal` | 任意 | 失敗しない `aesop_cat` 変種 | | |
| `aesop_graph` | 特化 | `aesop_graph` | 任意 | グラフライブラリ用 `aesop` | | |
| `aesop_graph?` | 特化 | `aesop_graph?` | 任意 | `aesop_graph` の提案版 | | |
| `aesop_graph_nonterminal` | 特化 | `aesop_graph_nonterminal` | 任意 | 失敗しない `aesop_graph` | | |
| `aesop_mat` | 特化 | `Matroid.aesop_mat` | 任意 | マトロイドの台集合包含証明 | | |
| `aesop_unfold` [→詳細](detail/自動化/aesop.md) | 自動化 | `Aesop.tacticAesop_unfold_` | 任意 | aesop コンテキストで定義展開 | 親ページ（`aesop`）と同様 | 親ページ（`aesop`）と同様 |
| `algebraize` | 特化 | `Mathlib.Tactic.tacticAlgebraize__` | 任意 | `RingHom` を `Algebra` に変換 | | |
| `algebraize_only` | 特化 | `Mathlib.Tactic.tacticAlgebraize_only__` | 任意 | `Algebra` と `IsScalarTower` のみ追加 | | |
| `all_goals` [→詳細](detail/制御/all_goals.md) | 制御 | `Lean.Parser.Tactic.allGoals` | 任意 | 全ゴールにタクティク適用 | 分岐後の重複コードを排除・simp/omega 等と相性良い | 1つでも失敗するとロールバック・部分適用は any_goals を使うこと |
| `and_intros` | 導入 | `Lean.Parser.Tactic.tacticAnd_intros` | ∧ | `And.intro` を繰り返し適用 | | |
| `any_goals` [→詳細](detail/制御/any_goals.md) | 制御 | `Lean.Parser.Tactic.anyGoals` | 任意 | 成功したゴールのみ連結 | 部分的に解決できるゴールだけ処理・全滅時はエラーで安全 | どのゴールが解決されたか把握しにくい・全ゴール成功必要なら all_goals が厳密 |
| `apply_assumption` [→詳細](detail/補題適用/apply_assumption.md) | 補題適用 | `Lean.Parser.Tactic.applyAssumption` | 仮定依存 | 仮定からゴールに適用 | 仮定名不要でコンテキストが大きい場合に便利・自動化タクティクの構成要素として有効 | 複数マッチで意図しない仮定が適用される可能性・可読性の観点では `apply h` が望ましい |
| `apply_rfl` | 閉鎖 | `Lean.Parser.Tactic.applyRfl` | 等式 | `rfl` から `eq_refl` を除いた版 | | |
| `array_get_dec` | 特化 | `Array.tacticArray_get_dec` | 線形算術 | `sizeOf arr[i] < sizeOf arr` 証明 | | |
| `array_mem_dec` | 特化 | `Array.tacticArray_mem_dec` | 線形算術 | `a ∈ arr` から sizeOf 不等式証明 | | |
| `as_aux_lemma` | 制御 | `Lean.Parser.Tactic.as_aux_lemma` | 任意 | 結果を補助補題にラップ | | |
| `assumption'` [→詳細](detail/閉鎖/assumption.md) | 閉鎖 | `Mathlib.Tactic.tacticAssumption'` | 仮定依存 | 全ゴールに `assumption` を試行 | 親ページ（`assumption`）と同様 | 親ページ（`assumption`）と同様 |
| `assumption_mod_cast` [→詳細](detail/閉鎖/assumption.md) | 鋳型 | `Lean.Parser.Tactic.tacticAssumption_mod_cast_` | キャスト | キャスト正規化 + `assumption` | 親ページ（`assumption`）と同様 | 親ページ（`assumption`）と同様 |
| `attempt_all` | 制御 | `Lean.Parser.Tactic.attemptAll` | 任意 | `try?` 実装用内部補助 | | |
| `attempt_all_par` | 制御 | `Lean.Parser.Tactic.attemptAllPar` | 任意 | `try?` 並列実行用内部補助 | | |
| `aux_group₁` | 代数 | `Mathlib.Tactic.Group.aux_group₁` | 環式 | `group` 補助（簡約器のみ） | | |
| `aux_group₂` | 代数 | `Mathlib.Tactic.Group.aux_group₂` | 環式 | `group` 補助（指数正規化） | | |

---

### b

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `bddDefault` | 特化 | `Filter.tacticBddDefault` | 任意 | `IsBounded` のデフォルト証明 | | |
| `beta_reduce` [→詳細](detail/簡約/beta_reduce.md) | 簡約 | `Lean.Parser.Tactic.betaReduceTac` | 任意 | ゴール中のベータ簡約実行 | β簡約のみを surgical に適用 | β-レデックスがない場合は効果なし |
| `bicategory` | 特化 | `Mathlib.Tactic.Bicategory.Coherence.bicategory` | 等式 | 二圏等式を正規化して解く | | |
| `bicategory_coherence` | 特化 | `Mathlib.Tactic.BicategoryCoherence.bicategory_coherence` | 等式 | 二圏コヒーレンス定理で証明 | | |
| `bicategory_nf` | 特化 | `Mathlib.Tactic.BicategoryCoherence.bicategory_nf` | 等式 | 二圏 2-射を正規形に書換 | | |
| `bitwise_assoc_tac` | 特化 | `Nat.tacticBitwise_assoc_tac` | 等式 | ビット演算の結合性補助証明 | | |
| `borelize` | 特化 | `MeasureTheory.Tactic.borelize` | 任意 | ボレル可測性仮定の追加 | | |
| `bound` [→詳細](detail/算術/bound.md) | 算術 | `«tacticBound[_]»` | 線形算術 | `@[bound]` 補題で不等式再帰証明 | @[bound] 補題で非負性・単調性の不等式を再帰的に解決 | @[bound] 補題がないと失敗・算術とは別途使い分け必要 |
| `bv_check` | 特化 | `Lean.Parser.Tactic.bvCheck` | Decidable | LRAT ファイル使用の `bv_decide` | | |
| `bv_decide?` | 特化 | `Lean.Parser.Tactic.bvDecide?` | Decidable | `bv_decide` の提案版 | | |
| `bv_normalize` | 特化 | `Lean.Parser.Tactic.bvNormalize` | Decidable | ビットベクトル式を正規化 | | |
| `bv_omega` [→詳細](detail/特化/bv_omega.md) | 特化 | `Lean.Parser.Tactic.bvOmega` | 線形算術 | `omega` のビットベクトル版 | ビットベクタの線形算術を omega と同感覚で解決 | ビット演算（&・|）は解けない・bv_decide が必要 |
| `by_cases!` [→詳細](detail/分解/by_cases.md) | 分解 | `Mathlib.Tactic.tacticBy_cases!_:_` | 任意 | 古典論理版 `by_cases` | 親ページ（`by_cases`）と同様 | 親ページ（`by_cases`）と同様 |
| `by_contra!` [→詳細](detail/変換/by_contra.md) | 変換 | `Mathlib.Tactic.ByContra.byContra!` | False/変換後 | `by_contra` + `push_neg` | 親ページ（`by_contra`）と同様 | 親ページ（`by_contra`）と同様 |

---

### c

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `calc?` | 探索 | `Mathlib.Tactic.calcTacSyntax` | 等式 | `calc` ステップを提案 | | |
| `cancel_denoms` [→詳細](detail/代数/cancel_denoms.md) | 代数 | `Mathlib.Tactic.CancelDenoms.cancelDenomsTac` | 環式 | 分母をキャンセルして整数に変換 | ring/linarith の前処理として分母を自動消去 | Field インスタンスが必須・変数分母で失敗 |
| `case` [→詳細](detail/制御/case.md) | 制御 | `Lean.Parser.Tactic.case` | 任意 | 指定ケース名のゴールにフォーカス | ゴール順序に依存しない堅牢な証明スクリプト | ケース名を正確に知る必要あり |
| `case'` [→詳細](detail/制御/case.md) | 制御 | `Lean.Parser.Tactic.case'` | 任意 | `case` の非失敗版 | 親ページ（`case`）と同様 | 親ページ（`case`）と同様 |
| `cases'` [→詳細](detail/分解/cases.md) | 分解 | `Mathlib.Tactic.cases'` | 帰納型 | `cases` の後方互換変種 | 親ページ（`cases`）と同様 | 親ページ（`cases`）と同様 |
| `cases_first_enat` | 分解 | `ENat.tacticCases_first_enat` | 帰納型 | `ℕ∞` のケース分析 | | |
| `cases_type` [→詳細](detail/分解/cases.md) | 分解 | `Mathlib.Tactic.casesType` | 帰納型 | 指定型の仮定に `cases` | 親ページ（`cases`）と同様 | 親ページ（`cases`）と同様 |
| `cases_type!` [→詳細](detail/分解/cases.md) | 分解 | `Mathlib.Tactic.casesType!` | 帰納型 | `cases_type` の再帰版 | 親ページ（`cases`）と同様 | 親ページ（`cases`）と同様 |
| `casesm` [→詳細](detail/分解/cases.md) | 分解 | `Mathlib.Tactic.casesM` | 帰納型 | パターンマッチで仮定に `cases` | 親ページ（`cases`）と同様 | 親ページ（`cases`）と同様 |
| `casesm!` [→詳細](detail/分解/cases.md) | 分解 | `Mathlib.Tactic.casesM!` | 帰納型 | `casesm` の繰り返し版 | 親ページ（`cases`）と同様 | 親ページ（`cases`）と同様 |
| `cat_disch` | 特化 | `CategoryTheory.cat_disch` | 任意 | 圏論ゴール自動解決 | | |
| `cbv` [→詳細](detail/簡約/cbv.md) | 簡約 | `Lean.Parser.Tactic.cbv` | 任意 | コール・バイ・バリュー簡約 | 完全 CBV 評価が必要な場合に有用 | 大規模式では非常に遅い・simp で代替可な場合が多い |
| `cfc_cont_tac` | 特化 | `cfcContTac` | 任意 | CFC 連続性の自動証明 | | |
| `cfc_tac` | 特化 | `cfcTac` | 任意 | CFC 述語充足の自動証明 | | |
| `cfc_zero_tac` | 特化 | `cfcZeroTac` | 等式 | CFC 非ユニタル版 `f 0 = 0` 証明 | | |
| `change?` | 変換 | `change?` | 変換後 | `change` の提案版 | | |
| `check_compositions` | 特化 | `CategoryTheory.check_compositions` | 等式 | 圏論合成の整合性検証 | | |
| `choose` [→詳細](detail/特化/choose.md) | 特化 | `Mathlib.Tactic.Choose.choose` | ∀/∃ | `∀∃` 仮定から選択関数抽出 | ∀∃パターンから選択関数を自動構成・後続で自由利用可 | Classical.choice 依存で非構成的 |
| `choose!` [→詳細](detail/特化/choose.md) | 特化 | `Mathlib.Tactic.Choose.choose!` | ∀/∃ | `choose` の命題引数依存除去版 | 親ページ（`choose`）と同様 | 親ページ（`choose`）と同様 |
| `classical` [→詳細](detail/変換/classical.md) | 変換 | `Lean.Parser.Tactic.classical` | 任意 | `Classical.propDecidable` を追加 | Decidable 不要で by_cases 相当の分岐が可能に | 構成的証明が失われる・#eval 実行で問題の可能性 |
| `clean` | 簡約 | `Mathlib.Tactic.tacticClean_` | 任意 | （非推奨）`exact clean% t` | | |
| `clean_wf` | 制御 | `tacticClean_wf` | 任意 | 停止性証明の内部クリーンアップ | | |
| `clear` [→詳細](detail/変換/clear.md) | 変換 | `Lean.Parser.Tactic.clear` | 仮定依存 | 仮定をコンテキストから削除 | 不要な仮定の除去でコンテキスト整理・依存エラー解消 | 依存先の仮定は除去不可・不可逆操作 |
| `clear!` [→詳細](detail/変換/clear.md) | 変換 | `Mathlib.Tactic.clear!` | 仮定依存 | 依存仮定も同時削除 | 親ページ（`clear`）と同様 | 親ページ（`clear`）と同様 |
| `clear_` [→詳細](detail/変換/clear.md) | 変換 | `Mathlib.Tactic.clear_` | 仮定依存 | `_` 始まりの仮定を全削除 | 親ページ（`clear`）と同様 | 親ページ（`clear`）と同様 |
| `clear_aux_decl` | 変換 | `Mathlib.Tactic.clearAuxDecl` | 仮定依存 | 全補助宣言を削除 | | |
| `clear_value` [→詳細](detail/変換/clear.md) | 変換 | `Mathlib.Tactic.clearValue` | 仮定依存 | `let` 値定義を削除 | 親ページ（`clear`）と同様 | 親ページ（`clear`）と同様 |
| `coherence` | 特化 | `Mathlib.Tactic.Coherence.coherence` | 等式 | モノイダル圏コヒーレンス定理 | | |
| `compareOfLessAndEq_rfl` | 閉鎖 | `compareOfLessAndEq_rfl` | 等式 | `compareOfLessAndEq` を `rfl` で閉じる | | |
| `compute_degree` [→詳細](detail/特化/compute_degree.md) | 特化 | `Mathlib.Tactic.ComputeDegree.computeDegree` | 等式/線形算術 | 多項式の次数を自動計算 | 多項式次数の計算を完全自動化・natDegree 等を広くカバー | Polynomial R 以外不可・係数ゼロ時にサブゴール残 |
| `compute_degree!` [→詳細](detail/特化/compute_degree.md) | 特化 | `Mathlib.Tactic.ComputeDegree.computeDegree!` | 等式/線形算術 | `compute_degree` の積極版 | 親ページ（`compute_degree`）と同様 | 親ページ（`compute_degree`）と同様 |
| `congr!` [→詳細](detail/変換/congr.md) | 変換 | `Congr!.congr!` | 等式 | `congr` の強力版（深い展開） | 親ページ（`congr`）と同様 | 親ページ（`congr`）と同様 |
| `congrm` [→詳細](detail/変換/congrm.md) | 変換 | `Mathlib.Tactic.congrM` | 等式 | パターンで lhs/rhs 同時マッチング | 複雑な等式でパターン指定が可能・lhs/rhs を同時マッチ | パターンがマッチしないと失敗・congr より構文が複雑 |
| `congrm?` [→詳細](detail/変換/congr.md) | 変換 | `tacticCongrm?` | 等式 | `congrm` の提案版 | 親ページ（`congr`）と同様 | 親ページ（`congr`）と同様 |
| `constructorm` | 導入 | `Mathlib.Tactic.constructorM` | 帰納型 | パターンマッチでコンストラクタ適用 | | |
| `continuity` [→詳細](detail/特化/continuity.md) | 特化 | `tacticContinuity` | 任意 | `@[continuity]` で `Continuous f` 解決 | Continuous f の構造的証明を全自動化・@[continuity] で拡張可 | ゴールが Continuous f 形でないと不可 |
| `continuity?` [→詳細](detail/特化/continuity.md) | 特化 | `tacticContinuity?` | 任意 | `continuity` の提案版 | 親ページ（`continuity`）と同様 | 親ページ（`continuity`）と同様 |
| `contrapose` [→詳細](detail/変換/contrapose.md) | 変換 | `Mathlib.Tactic.Contrapose.contrapose` | ∀/→ | 対偶を取る | 対偶が直接証明より容易な場合に証明を劇的に簡潔化 | P→Q 形でないと不可・否定整理に push_neg が必要 |
| `contrapose!` [→詳細](detail/変換/contrapose.md) | 変換 | `Mathlib.Tactic.Contrapose.contrapose!` | ∀/→ | `contrapose` + `push_neg` | 親ページ（`contrapose`）と同様 | 親ページ（`contrapose`）と同様 |
| `conv'` [→詳細](detail/書換/conv.md) | 書換 | `Lean.Parser.Tactic.Conv.convTactic` | 任意 | conv ゴール変換なしの `conv` | 親ページ（`conv`）と同様 | 親ページ（`conv`）と同様 |
| `conv?` [→詳細](detail/書換/conv.md) | 書換 | `Mathlib.Tactic.Conv.tacticConv?` | 任意 | `conv` の提案ウィジェット | 親ページ（`conv`）と同様 | 親ページ（`conv`）と同様 |
| `conv_lhs` [→詳細](detail/書換/conv_lhs.md) | 書換 | `Mathlib.Tactic.Conv.convLHS` | 等式 | 左辺に `conv` 適用 | 等式左辺のみを conv で精密変形・余計な修正なし | ゴールが等式でないと使えない・lhs が明確でない場合は conv を使うこと |
| `conv_rhs` [→詳細](detail/書換/conv_rhs.md) | 書換 | `Mathlib.Tactic.Conv.convRHS` | 等式 | 右辺に `conv` 適用 | 等式右辺のみを conv で精密変形・余計な修正なし | ゴールが等式でないと使えない・rhs が明確でない場合は conv を使うこと |
| `convert` [→詳細](detail/補題適用/convert.md) | 補題適用 | `Mathlib.Tactic.convert` | 仮定依存 | 差分をサブゴールにする `exact` | exact が失敗する「ほぼ合っている」補題の適用に有効 | congr 分解が過剰でサブゴール大量発生の恐れ |
| `convert_to` | 補題適用 | `Mathlib.Tactic.convertTo` | 変換後 | ゴールを指定式に変更 | | |
| `cutsat` | 算術 | `Lean.Parser.Tactic.cutsat` | 線形算術 | 線形整数算術（`lia` ラッパー） | | |

---

### d

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `dbg_trace` | デバッグ | `Lean.Parser.Tactic.dbgTrace` | 任意 | デバッグメッセージ表示 | | |
| `decide_cbv` | 自動化 | `Lean.Parser.Tactic.decide_cbv` | Decidable | CBV 正規化版 `decide` | | |
| `decreasing_tactic` | 制御 | `tacticDecreasing_tactic` | 任意 | 停止性証明デフォルト | | |
| `decreasing_trivial` | 制御 | `tacticDecreasing_trivial` | 任意 | 停止性基本ケース証明 | | |
| `decreasing_trivial_pre_omega` | 制御 | `tacticDecreasing_trivial_pre_omega` | 任意 | omega なし停止性証明 | | |
| `decreasing_with` | 制御 | `tacticDecreasing_with_` | 任意 | 指定タクティクで停止性証明 | | |
| `delta` [→詳細](detail/簡約/delta.md) | 簡約 | `Lean.Parser.Tactic.delta` | 任意 | デルタ展開（低レベル） | unfold が失敗する定義もδ展開可能 | 再帰関数展開で内部表現露出・最後の手段として使用 |
| `deriving_LawfulEq_tactic` | 制御 | `tacticDeriving_LawfulEq_tactic` | 任意 | `LawfulEq` 自動導出用内部 | | |
| `deriving_LawfulEq_tactic_step` | 制御 | `tacticDeriving_LawfulEq_tactic_step` | 任意 | 上記の単一ステップ版 | | |
| `deriving_ReflEq_tactic` | 制御 | `tacticDeriving_ReflEq_tactic` | 任意 | `ReflEq` 自動導出用内部 | | |
| `discrete_cases` | 特化 | `CategoryTheory.discreteCases` | 帰納型 | 離散圏のケース分析 | | |
| `done` [→詳細](detail/制御/done.md) | 制御 | `Lean.Parser.Tactic.done` | 任意 | 残りゴールがあれば失敗 | 証明完了を明示的にアサートして将来の回帰を早期検出 | 証明未完成の段階では使えない |
| `dsimp!` [→詳細](detail/簡約/dsimp.md) | 簡約 | `Lean.Parser.Tactic.tacticDsimp!_` | 任意 | `dsimp` の積極版 | 親ページ（`dsimp`）と同様 | 親ページ（`dsimp`）と同様 |
| `dsimp?` [→詳細](detail/簡約/dsimp.md) | 簡約 | `Lean.Parser.Tactic.dsimpTrace` | 任意 | `dsimp` の補題リスト提案版 | 親ページ（`dsimp`）と同様 | 親ページ（`dsimp`）と同様 |
| `dsimp?!` [→詳細](detail/簡約/dsimp.md) | 簡約 | `Lean.Parser.Tactic.tacticDsimp?!_` | 任意 | `dsimp?` の積極版 | 親ページ（`dsimp`）と同様 | 親ページ（`dsimp`）と同様 |

---

### e

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `eapply` [→詳細](detail/補題適用/eapply.md) | 補題適用 | `Lean.Parser.Tactic.eapply` | 仮定依存 | ユニフィケーション後回し版 `apply` | 遅延ユニフィケーションで存在命題の witness を後回し可能 | メタ変数が未解決だと証明が完了しない |
| `econstructor` [→詳細](detail/導入/econstructor.md) | 導入 | `Lean.Parser.Tactic.econstructor` | 帰納型 | ユニフィケーション後回し版 `constructor` | witness を後回しにして帰納型ゴールを分解・メタ変数を残せる | メタ変数が未解決のまま残ると証明不完結 |
| `enat_to_nat` | 鋳型 | `ENat.tacticEnat_to_nat` | キャスト | `ℕ∞` → `ℕ` 変換 | | |
| `eq_refl` | 閉鎖 | `Lean.Parser.Tactic.tacticEq_refl` | 等式 | `a = a` を閉じる（低レベル rfl） | | |
| `erw` [→詳細](detail/書換/erw.md) | 書換 | `Lean.Parser.Tactic.tacticErw__` | 等式 | 高透明度版 `rw` | rw が失敗する型クラス展開を跨いで書き換え可能 | 意図しない位置の書換リスク・非推奨扱いの場合あり |
| `erw?` [→詳細](detail/書換/erw.md) | 書換 | `Lean.Parser.Tactic.erw?` | 等式 | `erw` の提案版 | 親ページ（`erw`）と同様 | 親ページ（`erw`）と同様 |
| `eta_expand` [→詳細](detail/簡約/eta_expand.md) | 簡約 | `Lean.Parser.Tactic.etaExpand` | 任意 | イータ展開 | ラムダ式に展開し内部項へアクセスしやすくなる | 式が冗長になる・eta_reduce で元に戻せる |
| `eta_reduce` [→詳細](detail/簡約/eta_reduce.md) | 簡約 | `Lean.Parser.Tactic.etaReduceTac` | 任意 | イータ簡約 | 冗長な λx => f x を f に簡約・式を簡潔化 | η-レデックスがないと効果なし |
| `eta_struct` | 簡約 | `Lean.Parser.Tactic.etaStruct` | 任意 | 構造体イータ簡約 | | |
| `exact_mod_cast` [→詳細](detail/鋳型/exact_mod_cast.md) | 鋳型 | `Lean.Parser.Tactic.tacticExact_mod_cast_` | キャスト | キャスト正規化 + `exact` | キャストの差異だけなら1行で証明を閉じられる | キャスト以外の差異があれば失敗 |
| `exacts` [→詳細](detail/閉鎖/exacts.md) | 閉鎖 | `Batteries.Tactic.exacts` | 仮定依存 | `exact` のリスト版 | 複数の exact 候補を 1 行で試行・リスト列挙が簡潔 | 全候補が失敗すると全体失敗・候補数が多いと読みにくい |
| `existsi` | 導入 | `Mathlib.Tactic.existsi` | ∃ | （非推奨）`exists` の旧称 | | |
| `expose_names` | 制御 | `Lean.Parser.Tactic.exposeNames` | 任意 | アクセス不可能名を変換 | | |
| `ext1` [→詳細](detail/導入/ext1.md) | 導入 | `Lean.Elab.Tactic.Ext.tacticExt1___` | 関数等式 | `ext` の1ステップ版 | 外延性を 1 ステップだけ適用・意図外の過剰分解を防止 | 多段階分解には ext が簡潔・手動で繰り返す必要あり |
| `extract_goal` [→詳細](detail/デバッグ/extract_goal.md) | デバッグ | `Mathlib.Tactic.extractGoalTac` | 任意 | ゴールをスタンドアロン定理として提示 | sorry ゴールを独立補題として抽出・デバッグに有用 | Mathlib 依存・最終証明前に削除すること |
| `extract_lets` [→詳細](detail/変換/extract_lets.md) | 変換 | `Lean.Parser.Tactic.extractLets` | 任意 | `let` 式をローカル定義に抽出 | let 束縛をコンテキストに抽出・induction 等の前処理に有用 | let 束縛がないと効果なし |

---

### f

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `fail` [→詳細](detail/制御/fail.md) | 制御 | `Lean.Parser.Tactic.fail` | 任意 | 常に失敗 | 「ここには到達しない」テストとして機能・メタプログラミング向け | 証明を進展または閉じることができない |
| `fail_if_no_progress` [→詳細](detail/制御/fail_if_no_progress.md) | 制御 | `Mathlib.Tactic.failIfNoProgress` | 任意 | 進行しなければ失敗 | repeat の停止条件として機能・無効タクティクの検出 | 仮定変化は進捗ありと判定される場合あり |
| `fail_if_success` [→詳細](detail/制御/fail_if_success.md) | 制御 | `Lean.Parser.Tactic.failIfSuccess` | 任意 | 成功したら失敗（否定テスト） | タクティクが成功しないことをアサート・否定テストに有用 | 証明を進展させない・デバッグ・テスト専用 |
| `false_or_by_contra` | 変換 | `Lean.Parser.Tactic.falseOrByContra` | False | ゴールを `False` に変換 | | |
| `fapply` [→詳細](detail/補題適用/fapply.md) | 補題適用 | `Batteries.Tactic.tacticFapply_` | 仮定依存 | 出現順サブゴール版 `apply` | apply のサブゴール出現順を固定・メタ変数ユニフィケーション回避 | 推論可能な引数も冗長なサブゴールになる |
| `fconstructor` [→詳細](detail/導入/fconstructor.md) | 導入 | `tacticFconstructor` | 帰納型 | サブゴール順序固定版 `constructor` | constructor のサブゴール順序を固定・apply の代替として明確 | constructor で十分な場合は不要・サブゴール順序が constructor と異なる場合に使用 |
| `field` [→詳細](detail/代数/field.md) | 代数 | `Mathlib.Tactic.Field.field` | 環式 | `field_simp` + `ring` | field_simp + ring を自動適用・体の等式証明を1行で完結 | 分母 ≠ 0 の証明が見つからないと失敗・field_simp が解決できない場合は手動対応 |
| `field_simp_discharge` | 代数 | `Mathlib.Tactic.FieldSimp.discharge` | 環式 | `field_simp` の非ゼロディスチャージャー | | |
| `filter_upwards` [→詳細](detail/特化/filter_upwards.md) | 特化 | `Mathlib.Tactic.filterUpwards` | 任意 | フィルターゴールを ∀ 形に変換 | フィルター論法の定型証明手順を1行に圧縮 | フィルター以外のコンテキストでは使えない |
| `fin_cases` [→詳細](detail/分解/fin_cases.md) | 分解 | `Mathlib.Tactic.FinCases.finCasesStx` | 帰納型 | 有限型の全要素列挙ケース分析 | Fin n 等の有限型を全列挙して網羅的に証明可能 | n が大きいとサブゴール爆発・n が変数なら使えない |
| `fin_omega` | 算術 | `Fin.tacticFin_omega` | 線形算術 | `Fin` 不等式を `omega` に渡す | | |
| `find` | 探索 | `Mathlib.Tactic.Find.tacticFind` | 任意 | `apply` 可能な定義・定理検索 | | |
| `finiteness` [→詳細](detail/特化/finiteness.md) | 特化 | `tacticFiniteness` | 任意 | `@[finiteness]` で有限性証明 | @[finiteness] 補題で有限性を全自動証明 | 適切な @[finiteness] 補題がないと失敗 |
| `finiteness?` | 特化 | `tacticFiniteness?` | 任意 | `finiteness` の提案版 | | |
| `finiteness_nonterminal` | 特化 | `tacticFiniteness_nonterminal` | 任意 | 失敗しない `finiteness` | | |
| `first` [→詳細](detail/制御/first.md) | 制御 | `Lean.Parser.Tactic.first` | 任意 | 成功するまで順番に試す | 宣言的な分岐記述・cases 後の各ケースを共通処理 | 成功タクティクが不明・先頭が部分成功なら停止 |
| `first_par` | 制御 | `Lean.Parser.Tactic.firstPar` | 任意 | `try?` の並列実行版内部 | | |
| `focus` [→詳細](detail/制御/focus.md) | 制御 | `Lean.Parser.Tactic.focus` | 任意 | メインゴールにフォーカス | 1ゴールに集中・意図しないゴールへの影響を防止 | メインゴール未完成でエラー・「·」で十分な場合も多い |
| `forward` | 自動化 | `Aesop.Frontend.tacticForward____` | 任意 | `aesop` 前向き推論の手動適用 | | |
| `forward?` | 自動化 | `Aesop.Frontend.tacticForward?____` | 任意 | `forward` の提案版 | | |
| `frac_tac` | 特化 | `RatFunc.tacticFrac_tac` | 等式 | `K⟮X⟯` の等式操作 | | |
| `fun_cases` [→詳細](detail/分解/fun_cases.md) | 分解 | `Lean.Parser.Tactic.funCases` | 帰納型 | 関数定義に従うケース分析 | 関数の各パターンに対応した自然なケース分割 | 帰納法仮説は生成されない・fun_induction を使うこと |
| `fun_induction` [→詳細](detail/分解/fun_induction.md) | 分解 | `Lean.Parser.Tactic.funInduction` | 帰納型 | 関数の再帰構造に従う帰納法 | 再帰関数のパターンに完全一致する帰納法・IH が自動生成 | 相互再帰関数に非対応の場合あり |
| `fun_prop` [→詳細](detail/特化/fun_prop.md) | 特化 | `Mathlib.Meta.FunProp.funPropTacStx` | 任意 | `@[fun_prop]` で `P f` 証明 | Continuous/Differentiable 等を統一インターフェースで解決 | 複雑な関数では遅い・非関数プロパティには使えない |

---

### g

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `gcongr` [→詳細](detail/特化/gcongr.md) | 特化 | `Mathlib.Tactic.GCongr.tacticGcongr__` | 等式/線形算術 | `@[gcongr]` で不等式分解 | 不等式の構造分解を自動化・@[gcongr] で独自補題を拡張可 | @[gcongr] 未登録演算には使えない |
| `gcongr?` [→詳細](detail/特化/gcongr.md) | 特化 | `Mathlib.Tactic.GCongr.tacticGcongr?` | 等式/線形算術 | `gcongr` の提案版 | 親ページ（`gcongr`）と同様 | 親ページ（`gcongr`）と同様 |
| `gcongr_discharger` [→詳細](detail/特化/gcongr.md) | 特化 | `Mathlib.Tactic.GCongr.gcongr_discharger` | 任意 | `gcongr` サブゴールディスチャージャー | 親ページ（`gcongr`）と同様 | 親ページ（`gcongr`）と同様 |
| `generalize` [→詳細](detail/変換/generalize.md) | 変換 | `Lean.Parser.Tactic.generalize` | 任意 | 式を新変数で一般化 | induction 前の一般化で帰納法仮説を強化・h: e=x で元情報を保持可 | 一般化しすぎると証明不能になる場合あり |
| `generalize'` | 変換 | `«tacticGeneralize'_:_=_»` | 任意 | `generalize` の後方互換版 | | |
| `generalize_proofs` [→詳細](detail/変換/generalize_proofs.md) | 変換 | `Mathlib.Tactic.GeneralizeProofs.generalizeProofsStx` | 任意 | 証明項を変数に抽出 | ゴール内の証明項を変数に抽出・induction 等の前処理に有用 | 一般化しすぎると証明が複雑化する場合あり |
| `get_elem_tactic` [→詳細](detail/特化/get_elem_tactic.md) | 特化 | `tacticGet_elem_tactic` | 線形算術 | `arr[i]` の範囲証明自動化 | arr[i] の範囲証明を omega を使って自動生成 | 複雑な条件式は omega で解けず手動証明が必要 |
| `get_elem_tactic_extensible` | 特化 | `tacticGet_elem_tactic_extensible` | 線形算術 | `get_elem_tactic` の拡張版 | | |
| `get_elem_tactic_trivial` | 特化 | `tacticGet_elem_tactic_trivial` | 線形算術 | （非推奨）↑を使用 | | |
| `ghost_calc` | 特化 | `WittVector.Tactic.ghostCalc` | 等式 | ウィットベクトル多項式等式 | | |
| `ghost_fun_tac` | 特化 | `WittVector.Tactic.ghostFunTac` | 等式 | ウィットベクトル幽霊射計算 | | |
| `ghost_simp` | 特化 | `WittVector.Tactic.tacticGhost_simp___` | 等式 | ウィットベクトル幽霊写像簡約 | | |
| `grewrite` [→詳細](detail/書換/grewrite.md) | 書換 | `Mathlib.Tactic.GRewrite.grewriteStx` | 等式 | 一般化された書き換え | 合同性を利用した柔軟な書き換え・型クラス等式にも対応 | 挙動が rw より予測困難・通常は rw/simp_rw を優先 |
| `grind?` [→詳細](detail/自動化/grind.md) | 自動化 | `Lean.Parser.Tactic.grindTrace` | 任意 | `grind only` の最小構成提案 | 親ページ（`grind`）と同様 | 親ページ（`grind`）と同様 |
| `grind_linarith` | 算術 | `Lean.Parser.Tactic.grind_linarith` | 線形算術 | 線形算術限定 `grind` | | |
| `grind_order` | 算術 | `Lean.Parser.Tactic.grind_order` | 線形算術 | 順序関係限定 `grind` | | |
| `grobner` | 代数 | `Mathlib.Tactic.Polyrith.grobner` / `Lean.Parser.Tactic.grobner` | 環式 | Gröbner 基底で多項式等式証明 | | |
| `group` [→詳細](detail/代数/group.md) | 代数 | `Mathlib.Tactic.Group.group` | 環式 | 群の等式を正規化して証明 | 非可換群でも群の公理だけで等式を自動証明 | 加法的群は不可・abel を使うこと |
| `grw` [→詳細](detail/書換/grewrite.md) | 書換 | `Mathlib.Tactic.GRewrite.grwStx` | 等式 | `grewrite` の糖衣構文 | 合同性を利用した柔軟な書き換え・型クラス等式にも対応 | 挙動が rw より予測困難・通常は rw/simp_rw を優先 |
| `guard_expr` [→詳細](detail/デバッグ/guard_expr.md) | デバッグ | `Lean.Parser.Tactic.guardExpr` | 任意 | 式の等価性テスト | 式の等価性を静的にアサート・証明中の状態検証に有用 | デバッグ専用・証明を進展させない・最終証明前に削除すること |
| `guard_goal_nums` | デバッグ | `Lean.Parser.Tactic.guardGoalNums` | 任意 | ゴール数がn個であることをテスト | | |
| `guard_hyp` [→詳細](detail/デバッグ/guard_hyp.md) | デバッグ | `Lean.Parser.Tactic.guardHyp` | 任意 | 仮定の型・値一致テスト | 仮定の型・値を静的にテスト・中間状態の検証に有用 | デバッグ専用・証明を進展させない・最終証明前に削除すること |
| `guard_hyp_nums` | デバッグ | `guardHypNums` | 任意 | 仮定の個数テスト | | |
| `guard_target` [→詳細](detail/デバッグ/guard_target.md) | デバッグ | `Lean.Parser.Tactic.guardTarget` | 任意 | ゴールターゲットの等価テスト | ゴール型を静的にアサート・意図通りかを確認 | デバッグ専用・証明を進展させない・最終証明前に削除すること |

---

### h・i

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `have'` [→詳細](detail/補題適用/have'.md) | 補題適用 | `Lean.Parser.Tactic.tacticHave'_` | 任意 | `have` の変種（let に近い挙動） | have に近い構文で let 的な束縛を導入 | have と微妙に挙動が異なる・通常は have を使うこと |
| `haveI` [→詳細](detail/補題適用/haveI.md) | 補題適用 | `Lean.Parser.Tactic.haveI` | 任意 | インスタンスとして `have` | 型クラスインスタンスを仮定として透明に追加 | 通常の have と異なり不透明な仮定として扱われる |
| `hint` [→詳細](detail/探索/hint.md) | 探索 | `Mathlib.Tactic.Hint.hintStx` | 任意 | 登録タクティクを試して報告 | どのタクティクが有効か一括発見・学習・探索時に有用 | 全試行で遅い・最終証明には残さない |
| `ident` | 制御 | `Lean.Parser.Tactic.unknown` | 任意 | 未知タクティク識別子（エラー） | | |
| `induction'` [→詳細](detail/分解/induction.md) | 分解 | `Mathlib.Tactic.induction'` | 帰納型 | `induction` の後方互換変種 | 親ページ（`induction`）と同様 | 親ページ（`induction`）と同様 |
| `infer_instance` [→詳細](detail/閉鎖/infer_instance.md) | 閉鎖 | `Lean.Parser.Tactic.tacticInfer_instance` | 任意 | 型クラス推論でゴール閉鎖 | 型クラスインスタンス証明をワンショットで閉じる | インスタンス未登録・複雑クラス階層でタイムアウトの可能性 |
| `infer_param` | 閉鎖 | `Mathlib.Tactic.inferOptParam` | 任意 | optParam/autoParam のデフォルト値 | | |
| `inhabit` [→詳細](detail/変換/inhabit.md) | 変換 | `Lean.Elab.Tactic.inhabit` | 任意 | `Nonempty α` → `Inhabited α` | Nonempty α から Inhabited α を生成・古典的存在証明を前処理 | 古典論理に依存・constructive な証明が失われる |
| `init_ring` | 特化 | `WittVector.initRing` | 等式 | `init` 環演算保存の補助 | | |
| `injection` [→詳細](detail/分解/injection.md) | 分解 | `Lean.Parser.Tactic.injection` | 等式 | コンストラクタ単射性で等式分解 | コンストラクタ単射性で等式を直接分解・矛盾も自動導出 | コンストラクタの等式でない仮定には不可 |
| `injections` [→詳細](detail/分解/injection.md) | 分解 | `Lean.Parser.Tactic.injections` | 等式 | `injection` の再帰版 | 親ページ（`injection`）と同様 | 親ページ（`injection`）と同様 |
| `interval_cases` [→詳細](detail/分解/interval_cases.md) | 分解 | `Mathlib.Tactic.IntervalCases.intervalCases` | 線形算術 | 区間内の値を全列挙ケース分析 | 上下界の仮定から範囲を自動検出して全列挙 | 仮定なし・範囲が広いとサブゴール爆発 |
| `introv` [→詳細](detail/導入/introv.md) | 導入 | `Mathlib.Tactic.introv` | ∀/→ | 依存変数自動命名で導入 | ∀ 変数と仮定を自動命名で一括導入・命名の手間を省く | 自動名が意図と異なる場合あり・重要な仮定は intro で明示命名 |
| `isBoundedDefault` | 特化 | `Filter.tacticIsBoundedDefault` | 任意 | 完全束フィルター有界性 | | |
| `itauto` [→詳細](detail/自動化/itauto.md) | 自動化 | `Mathlib.Tactic.ITauto.itauto` | 任意 | 直観主義命題論理の恒真命題 | 直観主義命題論理に完全セitauto! で古典論理にも切替可 | 述語論理は不可・変数が多いと指数的に遅い |
| `itauto!` [→詳細](detail/自動化/itauto.md) | 自動化 | `Mathlib.Tactic.ITauto.itauto!` | 任意 | `itauto` の古典論理版 | 親ページ（`itauto`）と同様 | 親ページ（`itauto`）と同様 |
| `iterate` [→詳細](detail/制御/iterate.md) | 制御 | `Lean.Parser.Tactic.tacticIterate____` | 任意 | タクティクを n 回実行 | 回数を明示して意図通りの固定回数適用を保証 | 回数固定で型変化に脆弱・回数省略だと無限ループのリスク |

---

### l

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `let'` | 導入 | `Lean.Parser.Tactic.tacticLet'_` | 任意 | `let` の変種 | | |
| `letI` [→詳細](detail/導入/letI.md) | 導入 | `Lean.Parser.Tactic.letI` | 任意 | インスタンスとして `let` | 型クラス推論用の展開可能なインスタンスを追加・simp が展開可能 | 使いすぎると式が大きくなる・通常は haveI で十分 |
| `let_to_have` | 変換 | `Lean.Parser.Tactic.letToHave` | 任意 | `let` → `have` 変換 | | |
| `lia` [→詳細](detail/算術/lia.md) | 算術 | `Lean.Parser.Tactic.lia` | 線形算術 | 線形整数算術（`omega` 拡張後継） | Nat/Int 線形算術をオプションなしで自動解決 | 実数・非線形は不可タomega 失敗時はこちらも失敗の可能性 |
| `lift` [→詳細](detail/変換/lift.md) | 変換 | `Mathlib.Tactic.lift` | 仮定依存 | 条件付き型キャストの持ち上げ | Int→Nat 等の条件付き型変換を安全に実行 | CanLift インスタンスと持ち上げ条件の証明が必要 |
| `lift_lets` | 変換 | `Lean.Parser.Tactic.liftLets` | 任意 | `let` 束縛を外側に持ち上げ | | |
| `liftable_prefixes` | 制御 | `Lean.Parser.Tactic.liftablePrefixes` | 任意 | 持ち上げ可能プレフィックス特定 | | |
| `linarith!` [→詳細](detail/算術/linarith.md) | 算術 | `Mathlib.Tactic.tacticLinarith!_` | 線形算術 | `linarith` の積極版 | 親ページ（`linarith`）と同様 | 親ページ（`linarith`）と同様 |
| `linarith?` [→詳細](detail/算術/linarith.md) | 算術 | `Mathlib.Tactic.linarith?` | 線形算術 | `linarith only [...]` の最小セット提案 | 親ページ（`linarith`）と同様 | 親ページ（`linarith`）と同様 |
| `linarith?!` [→詳細](detail/算術/linarith.md) | 算術 | `Mathlib.Tactic.tacticLinarith?!_` | 線形算術 | `linarith?` の積極版 | 親ページ（`linarith`）と同様 | 親ページ（`linarith`）と同様 |
| `linear_combination'` [→詳細](detail/代数/linear_combination.md) | 代数 | `Mathlib.Tactic.LinearCombination'.linearCombination'` | 等式 | `linear_combination` の後方互換変種 | 親ページ（`linear_combination`）と同様 | 親ページ（`linear_combination`）と同様 |
| `linear_combination2` [→詳細](detail/代数/linear_combination.md) | 代数 | `Mathlib.Tactic.LinearCombination2.linearCombination2` | 等式 | `linear_combination` の別変種 | 親ページ（`linear_combination`）と同様 | 親ページ（`linear_combination`）と同様 |

---

### m

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `map_fun_tac` | 特化 | `WittVector.mapFun.tacticMap_fun_tac` | 等式 | `mapFun` 環演算保存の補助 | | |
| `map_tacs` [→詳細](detail/制御/map_tacs.md) | 制御 | `Batteries.Tactic.«tacticMap_tacs[_;]»` | 任意 | 各ゴールに対応タクティク適用 | 各ゴールに対応するタクティクを 1:1 で適用 | タクティク数とゴール数が一致しないと失敗 |
| `massumption` | 制御 | `Lean.Parser.Tactic.massumption` | 任意 | `SPred` 用 `assumption` | | |
| `match` [→詳細](detail/分解/match.md) | 分解 | `Lean.Parser.Tactic.match` | 帰納型 | タクティクモードのパターンマッチ | ターム側 match と同構文・複数値同時マッチが可能 | 帰納法仮説は生成されない・帰納法は induction を使うこと |
| `match_scalars` | 代数 | `Mathlib.Tactic.LinearCombination.matchScalars` | 等式 | モジュール等式のスカラー係数マッチング | | |
| `match_target` | 制御 | `Mathlib.Tactic.tacticMatch_target_` | 任意 | （非推奨）`guard_target` を使用 | | |
| `mcases` | 制御 | （複数） | 任意 | `SPred` 用 `cases`/`rcases` | | |
| `mclear` | 制御 | （複数） | 任意 | `SPred` 用 `clear` | | |
| `mconstructor` | 制御 | （複数） | 任意 | `SPred` 用 `constructor` | | |
| `mdup` | 制御 | `Lean.Parser.Tactic.mdup` | 任意 | `SPred` 仮定の複製 | | |
| `measurability` [→詳細](detail/特化/measurability.md) | 特化 | `Mathlib.Tactic.measurability` | 任意 | `@[measurability]` で可測性証明 | 可測性の構造的証明を全自動化シMeasurable 等を幅広くカバー | 非自明な可測性・大規模ゴールで探索が遅い可能性 |
| `measurability!` [→詳細](detail/特化/measurability.md) | 特化 | `measurability!` [→詳細](detail/特化/measurability.md) | 任意 | `measurability` の積極版 | 親ページ（`measurability`）と同様 | 親ページ（`measurability`）と同様 |
| `measurability!?` [→詳細](detail/特化/measurability.md) | 特化 | `measurability!?` [→詳細](detail/特化/measurability.md) | 任意 | `measurability!` の提案版 | 親ページ（`measurability`）と同様 | 親ページ（`measurability`）と同様 |
| `measurability?` [→詳細](detail/特化/measurability.md) | 特化 | `Mathlib.Tactic.measurability?` | 任意 | `measurability` の提案版 | 親ページ（`measurability`）と同様 | 親ページ（`measurability`）と同様 |
| `mem_tac` | 特化 | `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.tacticMem_tac` | 任意 | 射影スペクトル斉次部分の元属性証明 | | |
| `mexact` | 制御 | `Lean.Parser.Tactic.mexactMacro` | 任意 | `SPred` 用 `exact` | | |
| `mexfalso` | 制御 | `Lean.Parser.Tactic.mexfalso` | 任意 | `SPred` 用 `exfalso` | | |
| `mexists` | 制御 | `Lean.Parser.Tactic.mexists` | 任意 | `SPred` 用 `exists` | | |
| `mfld_set_tac` | 特化 | `Mathlib.Geometry.Manifold.mfldSetTac` | 任意 | 多様体地図変換の集合演算 | | |
| `mframe` | 制御 | `Lean.Parser.Tactic.mframe` | 任意 | `SPred` フレーム条件 | | |
| `mhave` | 制御 | `Lean.Parser.Tactic.mhave` | 任意 | `SPred` 用 `have` | | |
| `mintro` | 制御 | `Lean.Parser.Tactic.mintro` | 任意 | `SPred` 用 `intro` | | |
| `mleave` | 制御 | `Lean.Parser.Tactic.mleave` | 任意 | モナディック証明ブロックを抜ける | | |
| `mleft` | 制御 | `Lean.Parser.Tactic.mleft` | 任意 | `SPred` 用 `left` | | |
| `mod_cases` [→詳細](detail/分解/mod_cases.md) | 分解 | `Mathlib.Tactic.ModCases.modCasesStx` | 線形算術 | 剰余値でケース分析 | 剰余ベースのケース分析が1行で完了 | 法 m が大きいとケース爆発シNat と Int で剰余の挙動差異 |
| `module` [→詳細](detail/代数/module.md) | 代数 | `Mathlib.Tactic.Module.moduleStx` | 等式 | 加群・ベクトル空間の等式証明 | スカラー乗法を含む加群等式をワンショット証明 | 非線形スカラー演算・不等式は対象外 |
| `monicity` | 代数 | `Mathlib.Tactic.Polyrith.monicityStx` | 等式 | 多項式の最高次係数 = 1 証明 | | |
| `monicity!` | 代数 | `Mathlib.Tactic.Polyrith.monicity!Stx` | 等式 | `monicity` の積極版 | | |
| `mono` [→詳細](detail/特化/mono.md) | 特化 | `Mathlib.Tactic.Monotonicity.mono` | 線形算術 | `@[mono]` で不等式分解 | 不等式の単調性分解が直感的・@[mono] で独自補題を登録可 | gcongr の方が新しく推奨・登録補題数は少ない傍向 |
| `monoidal` | 特化 | `Mathlib.Tactic.Coherence.monoidal` | 等式 | モノイダル圏等式の正規化証明 | | |
| `monoidal_coherence` | 特化 | `Mathlib.Tactic.MonoidalCoherence.monoidal_coherence` | 等式 | マッグレーン一貫性定理 | | |
| `monoidal_nf` | 特化 | `Mathlib.Tactic.BicategoryCoherence.monoidal_nf` | 等式 | モノイダル圏の正規形書き換え | | |
| `monoidal_simps` | 特化 | `Mathlib.Tactic.BicategoryCoherence.monoidal_simps` | 等式 | モノイダル圏糖衣構文の展開 | | |
| `move_add` [→詳細](detail/代数/move_add.md) | 代数 | `Mathlib.MoveAdd.tacticMove_add_` | 環式 | 加算の項を右端に移動 | 指定項の並び替えで ring_nf 等との前処理に活用可 | 等式証明自体は行わない・並び替えのみ |
| `move_mul` [→詳細](detail/代数/move_add.md) | 代数 | `Mathlib.MoveAdd.tacticMove_mul_` | 環式 | 乗算の項を右端に移動 | 親ページ（`move_add`）と同様 | 親ページ（`move_add`）と同様 |
| `move_oper` [→詳細](detail/代数/move_add.md) | 代数 | `Mathlib.MoveAdd.moveOperTac` | 環式 | 二項演算の項を移動（汎用版） | 親ページ（`move_add`）と同様 | 親ページ（`move_add`）と同様 |
| `mpure` | 制御 | `Lean.Parser.Tactic.mpure` | 任意 | `SPred` 純粋命題取り出し | | |
| `mpure_intro` | 制御 | `Lean.Parser.Tactic.mpure_intro` | 任意 | `SPred` 純粋命題導入 | | |
| `mrefine` | 制御 | `Lean.Parser.Tactic.mrefine` | 任意 | `SPred` 用 `refine` | | |
| `mrename_i` | 制御 | `Lean.Parser.Tactic.mrename_i` | 任意 | `SPred` 用 `rename_i` | | |
| `mreplace` | 制御 | `Lean.Parser.Tactic.mreplace` | 任意 | `SPred` 用 `replace` | | |
| `mrevert` | 制御 | `Lean.Parser.Tactic.mrevert` | 任意 | `SPred` 用 `revert` | | |
| `mright` | 制御 | `Lean.Parser.Tactic.mright` | 任意 | `SPred` 用 `right` | | |
| `mspec` | 制御 | `Lean.Parser.Tactic.mspecMacro` | 任意 | Hoare トリプル仕様を適用 | | |
| `mspec_no_bind` | 制御 | `Lean.Parser.Tactic.mspecNoBindMacro` | 任意 | `mspec` の `bind` 分解なし版 | | |
| `mspec_no_simp` | 制御 | `Lean.Parser.Tactic.mspecNoSimpMacro` | 任意 | `mspec` の `simp` なし版 | | |
| `mspecialize` | 制御 | `Lean.Parser.Tactic.mspecialize` | 任意 | `SPred` 用 `specialize` | | |
| `mspecialize_pure` | 制御 | `Lean.Parser.Tactic.mspecialize_pure` | 任意 | 純粋命題仮定の `mspecialize` | | |
| `mstart` | 制御 | `Lean.Parser.Tactic.mstart` | 任意 | モナディック証明開始 | | |
| `mstop` | 制御 | `Lean.Parser.Tactic.mstop` | 任意 | モナディック証明終了 | | |
| `mv_bisim` | 変換 | `Lean.Parser.Tactic.mvBisimMacro` | 等式 | コインダクション（双模倣）等式証明 | | |
| `mvcgen` | 制御 | `Lean.Parser.Tactic.mvcgen` | 任意 | Hoare 論理検証条件生成器 | | |
| `mvcgen?` | 制御 | `Lean.Parser.Tactic.mvcgenHint` | 任意 | `mvcgen invariants?` に展開 | | |
| `mvcgen_trivial` | 制御 | `Lean.Parser.Tactic.tacticMvcgen_trivial` | 任意 | `mvcgen` 検証条件の自動解決 | | |
| `mvcgen_trivial_extensible` | 制御 | `Lean.Parser.Tactic.tacticMvcgen_trivial_extensible` | 任意 | `mvcgen_trivial` の拡張版 | | |

---

### n

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `next` [→詳細](detail/制御/next.md) | 制御 | `Lean.Parser.Tactic.«taticNext_=>_»` | 任意 | 次のゴールにフォーカス | ケース名不要でゴールにフォーカス・自動生成名のリネームも可 | ゴール順序依存・定義変更で壊れやすい |
| `nlinarith!` [→詳細](detail/算術/nlinarith.md) | 算術 | `Mathlib.Tactic.tacticNlinarith!_` | 非線形算術 | `nlinarith` の積極版 | 親ページ（`nlinarith`）と同様 | 親ページ（`nlinarith`）と同様 |
| `nofun` [→詳細](detail/閉鎖/nofun.md) | 閉鎖 | `Lean.Parser.Tactic.tacticNofun` | 帰納型 | `exact nofun` の糖衣構文 | 空パターン関数型ゴールを contradiction より簡潔に閉じる | ゴールが関数型でないと失敗 |
| `nomatch` [→詳細](detail/閉鎖/nomatch.md) | 閉鎖 | `Lean.Parser.Tactic.«taticNomatch_,,»` | 帰納型 | `exact nomatch h` の糖衣構文 | 空型の仮定で到達不能ケースを明示的に閉じる | 型が空でないと判定されたら失敗 |
| `noncomm_ring` [→詳細](detail/代数/noncomm_ring.md) | 代数 | `Mathlib.Tactic.NoncommRing.noncomm_ring` | 環式 | 非可換環の等式証明 | ring が使えない非可換環の等式を自動処理・行列・四元数等に有効 | 可換環なら ring を使うこと |
| `nontriviality` [→詳細](detail/特化/nontriviality.md) | 特化 | `Mathlib.Tactic.Nontriviality.nontriviality` | 任意 | `Nontrivial α` インスタンス追加 | 代数証明の Nontrivial 導入というボイラープレートを自動化 | 後続タクティクとの組み合わせ必須・単体ではゴール未閉 |
| `norm_cast0` | 鋳型 | `Lean.Parser.Tactic.tacticNorm_cast0` | キャスト | `norm_cast` の内部版 | | |
| `norm_num1` | 算術 | `Mathlib.Tactic.normNum1` | 等式/線形算術 | `norm_num` の単一ステップ版 | | |
| `nth_grewrite` [→詳細](detail/書換/nth_rw.md) | 書換 | `Mathlib.Tactic.GRewrite.nthGrewriteStx` | 等式 | `grewrite` の n 番目出現版 | 親ページ（`nth_rw`）と同様 | 親ページ（`nth_rw`）と同様 |
| `nth_grw` [→詳細](detail/書換/nth_rw.md) | 書換 | `Mathlib.Tactic.GRewrite.nthGrwStx` | 等式 | `grw` の n 番目出現版 | 親ページ（`nth_rw`）と同様 | 親ページ（`nth_rw`）と同様 |
| `nth_rewrite` [→詳細](detail/書換/nth_rw.md) | 書換 | `Mathlib.Tactic.nthRewriteSeq` | 等式 | `rewrite` の n 番目出現版 | 親ページ（`nth_rw`）と同様 | 親ページ（`nth_rw`）と同様 |
| `nth_rw` [→詳細](detail/書換/nth_rw.md) | 書換 | `Mathlib.Tactic.nthRwSeq` | 等式 | `rw` の n 番目出現版 | 番号指定で簡潔シconv 不要・構文は rw と同一 | 式の構造変化で番号ずれの可能性シconv の方が安定 |

---

### o

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `observe` [→詳細](detail/補題適用/observe.md) | 補題適用 | `Mathlib.Tactic.LibrarySearch.observe` | 任意 | `exact?` で新仮定を証明追加 | 型さえわかれば補題名不要で仮定を追加できる | ライブラリ検索に時間がかかる・存在しない型は失敗 |
| `observe?` | 補題適用 | `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_»` | 任意 | `observe` の提案版 | | |
| `on_goal` [→詳細](detail/制御/on_goal.md) | 制御 | `Batteries.Tactic.«tacticOn_goal-_=>_»` | 任意 | n 番目のゴールにタクティク適用 | ゴール番号を指定して特定ゴールのみを処理 | ゴール番号は動的で変動しやすく脆弱・case を使うこと |
| `open` [→詳細](detail/制御/open.md) | 制御 | `Lean.Parser.Tactic.open` | 任意 | タクティクブロック内で名前空間を開く | 修飾名を短縮・スコープ限定で名前衝突リスク低 | 多数の名前空間を開くと意図しない名前解決の可能性 |
| `order` [→詳細](detail/算術/order.md) | 算術 | `Mathlib.Tactic.Order.tacticOrder_` | 線形算術 | 順序のゴールを完全解決 | 抽象順序構造で < と ≤ 混在の推論を統一処理 | 算術演算を含む不等式は linarith を使うこと |
| `order_core` | 算術 | `Mathlib.Tactic.Order.order_core` | 線形算術 | `order` の矛盾探索コア | | |

---

### p

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `peel` [→詳細](detail/変換/peel.md) | 変換 | `Mathlib.Tactic.Peel.peel` | ∀/∃ | 量化子・フィルターの最外層を劑がす | ∀∃ ネスト分解シintro+specialize+obtain を1行に圧縮 | 量化子構造が仮定とゴールで対応しないと失敗 |
| `pi_lower_bound` | 特化 | `Real.«tacticPi_lower_bound[_,,]»` | 線形算術 | `a < π` の証明 | | |
| `pi_upper_bound` | 特化 | `Real.«tacticPi_upper_bound[_,,]»` | 線形算術 | `π < a` の証明 | | |
| `pick_goal` [→詳細](detail/制御/pick_goal.md) | 制御 | `Batteries.Tactic.«tacticPick_goal-_»` | 任意 | n 番目ゴールを先頭に移動 | 指定番号のゴールを先頭に移動・処理順を明示的に制御 | ゴール番号が動的で脆弱・on_goal の方が目的が明確 |
| `plausible` [→詳細](detail/特化/plausible.md) | 特化 | `plausibleSyntax` | 任意 | ランダムテストで反例探索 | 偉命題の早期発見・反例を具体値で報告してデバッグ容易 | 証明ではない（sorry が残る）・最終証明には残してはいけない |
| `pnat_positivity` | 算術 | `PNat.tacticPnat_positivity` | 線形算術 | `PNat` の正値自動証明 | | |
| `pnat_to_nat` | 鋳型 | `PNat.tacticPnat_to_nat` | キャスト | `PNat` → `Nat` 変換 | | |
| `pull` [→詳細](detail/書換/pull.md) | 書換 | `Mathlib.Tactic.Pull.pullStx` | 任意 | 定数を外側に引き上げ | 定数やスカラーを和・積の外側に引き上げる | push と使い分けに注意・意図した方向に動かないことも |
| `pure_coherence` | 特化 | `Mathlib.Tactic.Coherence.pure_coherence` | 等式 | モノイダル圏純粋射コヒーレンス | | |
| `pure_coherence_internal` | 特化 | `Mathlib.Tactic.Coherence.pure_coherence_internal` | 等式 | `pure_coherence` の内部版 | | |
| `push` [→詳細](detail/書換/push.md) | 書換 | `Mathlib.Tactic.Push.pushStx` | 任意 | 定数を内側に押し込む | 定数やスカラーを和・積の内側に押し込む | pull と使い分けに注意・意図した方向に動かないことも |

---

### q・r

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `qify` [→詳細](detail/鋳型/qify.md) | 鋳型 | `Mathlib.Tactic.Qify.qify` | キャスト | 整数・自然数 → 有理数ゴールに変換 | 整数除算の切り捨て問題を回避シfield_simp/ring との相性が良い | 有理数まで不要なら zify で十分 |
| `rcongr` [→詳細](detail/変換/rcongr.md) | 変換 | `Mathlib.Tactic.Congr.rcongr` | 等式 | `congr` + `ext`/`intro` の再帰版 | congr + ext/intro を再帰適用・バインダ内部まで分解 | 過剰分解で不要なサブゴールが生じる場合あり |
| `recover` [→詳細](detail/制御/recover.md) | 制御 | `Lean.Parser.Tactic.recover` | 任意 | 失敗後の状態回復 | エラー後も proof state を保持・複数タクティクのデバッグに有用 | ゴール順序・状態が予期せず変化する場合あり |
| `reduce` [→詳細](detail/簡約/reduce.md) | 簡約 | `Lean.Parser.Tactic.reduce` | 任意 | ゴールを完全簡約（kernel 計算） | カーネルレベルの完全簡約・decide 相当の評価が可能 | 大規模式で非常に遅い・最終手段として使用 |
| `reduce_mod_char` [→詳細](detail/簡約/reduce_mod_char.md) | 代数 | `Mathlib.Tactic.ReduceModChar.reduce_mod_char` | 環式 | 標数による定数消去の簡約 | ZMod n の具体的数値を自動簡約 | CharP インスタンスが必須・CharP が不明な場合は失敗 |
| `reduce_mod_char!` [→詳細](detail/簡約/reduce_mod_char.md) | 代数 | `Mathlib.Tactic.ReduceModChar.reduce_mod_char!` | 環式 | `reduce_mod_char` の積極版 | 親ページ（`reduce_mod_char`）と同様 | 親ページ（`reduce_mod_char`）と同様 |
| `refine'` [→詳細](detail/補題適用/refine'.md) | 補題適用 | `Lean.Parser.Tactic.refine'` | 仮定依存 | `refine` の自動サブゴール版 | _ を全サブゴールとして自動的に展開・柔軟なスキャフォールド | 暗黙引数も意図せずサブゴール化されることがある |
| `refine_lift` | 制御 | `Lean.Parser.Tactic.refineLift` | 任意 | `do` 記法 lift 用内部 | | |
| `refine_lift'` | 制御 | `Lean.Parser.Tactic.refineLift'` | 任意 | `refine_lift` の変種 | | |
| `refold_let` [→詳細](detail/簡約/refold_let.md) | 簡約 | `Mathlib.Tactic.refoldLetStx` | 任意 | 展開された `let` を元に折り畳む | 展開された let 定義を元の形に折り畳む・可読性向上 | let 定義が存在しない場合は効果なし |
| `rel` [→詳細](detail/特化/rel.md) | 特化 | `Mathlib.Tactic.GCongr.«tacticRel[_]»` | 等式/線形算術 | `@[gcongr]` でゴール分解 | @[gcongr] 補題で不等式・関係をゴール分解 | @[gcongr] 補題が登録されていないと失敗 |
| `rename` [→詳細](detail/変換/rename.md) | 変換 | `Lean.Parser.Tactic.rename` | 仮定依存 | 仮定の名前変更 | 自動生成名を可読名に変換して証明の読みやすさを向上 | 型パターン複数一致でエラーシwith 節で最初から命名が望ましい |
| `rename'` [→詳細](detail/変換/rename.md) | 変換 | `Mathlib.Tactic.rename'` | 仮定依存 | `rename` の変種 | 親ページ（`rename`）と同様 | 親ページ（`rename`）と同様 |
| `rename_bvar` [→詳細](detail/変換/rename.md) | 変換 | `Mathlib.Tactic.renameBVar` | 任意 | 束縛変数の名前変更（表示目的） | 親ページ（`rename`）と同様 | 親ページ（`rename`）と同様 |
| `rename_i` [→詳細](detail/変換/rename_i.md) | 変換 | `Lean.Parser.Tactic.renameI` | 任意 | アクセス不可能な名前を変更 | cases/match 後の † 名をアクセス可能な名前に変換 | アクセス不可能名がないとエラー・名前数が合わないとエラー |
| `repeat` [→詳細](detail/制御/repeat.md) | 制御 | `Lean.Parser.Tactic.tacticRepeat_` | 任意 | 失敗まで繰り返し | 繰り返し構造の分解を簡潔に記述・失敗で自動停止 | ゴール変化タクティクで無限ループのリスク |
| `repeat'` [→詳細](detail/制御/repeat.md) | 制御 | `Lean.Parser.Tactic.repeat'` | 任意 | 全サブゴールに再帰適用 | 親ページ（`repeat`）と同様 | 親ページ（`repeat`）と同様 |
| `repeat1` [→詳細](detail/制御/repeat.md) | 制御 | `Mathlib.Tactic.tacticRepeat1_` | 任意 | `repeat` の少なくとも1回版 | 親ページ（`repeat`）と同様 | 親ページ（`repeat`）と同様 |
| `repeat1'` [→詳細](detail/制御/repeat.md) | 制御 | `Lean.Parser.Tactic.repeat1'` | 任意 | `repeat'` の少なくとも1回版 | 親ページ（`repeat`）と同様 | 親ページ（`repeat`）と同様 |
| `restrict_tac` | 特化 | `TopCat.Presheaf.restrict_tac` | 任意 | 前層の制限マップ集合包含 | | |
| `restrict_tac?` | 特化 | `TopCat.Presheaf.restrict_tac?` | 任意 | `restrict_tac` の提案版 | | |
| `revert` [→詳細](detail/変換/revert.md) | 変換 | `Lean.Parser.Tactic.revert` | 仮定依存 | `intro` の逆（仮定をゴールに戻す） | induction 前の一般化シintro のタイミング制御に有用 | 依存仮定も自動リバートで予期しない変化が起きうる |
| `rewrite` [→詳細](detail/書換/rewrite.md) | 書換 | `Lean.Parser.Tactic.rewrite` | 等式 | 等式規則で書き換え | rfl を試みないため書き換え後のゴールを確認しやすい | rfl で閉じる場合は rw の方が簡潔 |
| `rewrite!` [→詳細](detail/書換/rewrite.md) | 書換 | `Mathlib.Tactic.DepRewrite.depRewriteSeq` | 等式 | 型依存書き換え（キャスト自動挿入） | 親ページ（`rewrite`）と同様 | 親ページ（`rewrite`）と同様 |
| `rfl'` [→詳細](detail/閉鎖/rfl.md) | 閉鎖 | `Lean.Parser.Tactic.tacticRfl'` | 等式 | `rfl` の全定義展開版 | 親ページ（`rfl`）と同様 | 親ページ（`rfl`）と同様 |
| `rfl_cat` | 特化 | `CategoryTheory.tacticRfl_cat` | 等式 | 圏論用 `rfl` | | |
| `rify` [→詳細](detail/鋳型/rify.md) | 鋳型 | `Mathlib.Tactic.Rify.rify` | キャスト | 整数・自然数 → 実数ゴールに変換 | nlinarith/polyrith 等の実数向ケタクティクと組み合わせ可 | 多くの場合 zify+omega で十分シrify は不要なことが多い |
| `ring!` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring!` | 環式 | `ring` の積極版 | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `ring1` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring1` | 環式 | 一ステップ環等式証明 | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `ring1!` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring1!` | 環式 | `ring1` の積極版 | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `ring1_nf` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring1NF` | 環式 | 正規形書き換え版（非再帰） | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `ring1_nf!` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ring1NF!` | 環式 | `ring1_nf` の積極版 | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `ring_nf!` [→詳細](detail/代数/ring.md) | 代数 | `Mathlib.Tactic.Ring.ringNF!` | 環式 | `ring_nf` の積極版 | 親ページ（`ring`）と同様 | 親ページ（`ring`）と同様 |
| `rotate_left` [→詳細](detail/制御/rotate_left.md) | 制御 | `Lean.Parser.Tactic.rotateLeft` | 任意 | ゴールを左方向に回転 | ゴールリストを左回転・処理順を多少制御 | ゴール番号依存で脆弱・on_goal/pick_goal より可読性が低い |
| `rotate_right` [→詳細](detail/制御/rotate_right.md) | 制御 | `Lean.Parser.Tactic.rotateRight` | 任意 | ゴールを右方向に回転 | ゴールリストを右回転・unfocus 相当の整理に使用 | ゴール順序の把握が困難・case 等より可読性が低い |
| `rsuffices` [→詳細](detail/変換/rsuffices.md) | 変換 | `Mathlib.Tactic.rsuffices` | 変換後 | `obtain` 記法の `suffices` | obtain 記法で十分条件に帰着・パターン分解と組み合わせ可 | サブゴール順序が suffices と逆・suffices との違いを意識 |
| `run_tac` [→詳細](detail/制御/run_tac.md) | 制御 | `Lean.Parser.Tactic.runTac` | 任意 | `TacticM Unit` の do ブロック実行 | TacticM メタプログラミングを即時実行・プロトタイパーに有用 | 可読性低・本番は elab でカスタムタクティクとして定義すべき |
| `rw!` [→詳細](detail/書換/rw.md) | 書換 | `Lean.Parser.Tactic.tacticRw!__` | 等式 | `rw` の積極版 | 親ページ（`rw`）と同様 | 親ページ（`rw`）と同様 |
| `rw??` [→詳細](detail/書換/rw.md) | 探索 | `Mathlib.Tactic.LibraryRewrite.tacticRw??` | 等式 | 部分式に書き換え候補提示 | 親ページ（`rw`）と同様 | 親ページ（`rw`）と同様 |
| `rw_mod_cast` [→詳細](detail/書換/rw_mod_cast.md) | 鋳型 | `Lean.Parser.Tactic.tacticRw_mod_cast___` | キャスト | キャスト正規化 + `rw` | キャスト正規化と rw を自動組み合わせ・型の不一致を吸収 | キャストが絡まない場合は通常の rw で十分 |
| `rw_search` | 探索 | `Mathlib.Tactic.RewriteSearch.tacticRw_search_` | 等式 | （削除済み）書き換え系列検索 | | |
| `rwa` [→詳細](detail/書換/rwa.md) | 書換 | `Lean.Parser.Tactic.tacticRwa__` | 等式 | `rw; assumption` の糖衣構文 | rw+assumption を1行に短縮シcore 組み込みで追加 import 不要 | assumption で閉じない場合はエラー |

---

### s

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `saturate` [→詳細](detail/自動化/saturate.md) | 自動化 | `Aesop.Frontend.saturate` | 任意 | `@[aesop]` 前向き補題で飽和 | 前向き推論で仮定を飽和させて後続証明を補助 | ゴール自体は閉じない・コンテキスト肥大化の恐れ |
| `saturate?` [→詳細](detail/自動化/saturate.md) | 自動化 | `Aesop.Frontend.saturate?` | 任意 | `saturate` の提案版 | 親ページ（`saturate`）と同様 | 親ページ（`saturate`）と同様 |
| `set` [→詳細](detail/変換/set.md) | 変換 | `Mathlib.Tactic.set` | 任意 | 式に名前付けてローカル定義導入 | 複雑な部分式に短い名前付け・等式仮定が自動追加 | Mathlib 必要・部分式マッチが厳密 |
| `set!` [→詳細](detail/変換/set.md) | 変換 | `Mathlib.Tactic.set!` | 任意 | `set` の積極版（仮定中も書換） | 親ページ（`set`）と同様 | 親ページ（`set`）と同様 |
| `set_option` [→詳細](detail/制御/set_option.md) | 制御 | `Lean.Parser.Tactic.set_option` | 任意 | ブロック内のみオプション設定 | maxHeartbeats 等を局所設定・デバッグ出力の局所化 | 大きすぎると型チェックが超低速・デバッグ用は commit 前に削除 |
| `show` [→詳細](detail/変換/show.md) | 変換 | `Lean.Parser.Tactic.show` | 変換後 | ユニファイするゴールをメインに | ゴールの型を明示して可読性向上・複数ゴール時の選択に有用 | ユニファイ不可ならエラーシchange とほぼ同等 |
| `show_term` [→詳細](detail/デバッグ/show_term.md) | デバッグ | `Lean.Parser.Tactic.showTerm` | 任意 | 証明項を `exact` 形式で表示 | タクティクが生成する証明項を可視化・項証明への書換候補取得 | 生成項が巨大になる場合あり・デバッグ専用 |
| `simp!` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp!_` | 任意 | `simp` の積極版（autoUnfold 有効） | 親ページ（`simp`）と同様 | 親ページ（`simp`）と同様 |
| `simp?!` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp?!_` | 任意 | `simp?` の積極版 | 親ページ（`simp`）と同様 | 親ページ（`simp`）と同様 |
| `simp_all!` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp_all!_` | 任意 | `simp_all` の積極版 | 親ページ（`simp_all`）と同様 | 親ページ（`simp_all`）と同様 |
| `simp_all?` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.simpAllTrace` | 任意 | `simp_all` の提案版 | 親ページ（`simp_all`）と同様 | 親ページ（`simp_all`）と同様 |
| `simp_all?!` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp_all?!_` | 任意 | `simp_all?` の積極版 | 親ページ（`simp_all`）と同様 | 親ページ（`simp_all`）と同様 |
| `simp_all_arith` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.simpAllArith` | 任意 | `simp_all` + 算術補題 | 親ページ（`simp_all`）と同様 | 親ページ（`simp_all`）と同様 |
| `simp_all_arith!` [→詳細](detail/簡約/simp_all.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp_all_arith!_` | 任意 | `simp_all_arith` の積極版 | 親ページ（`simp_all`）と同様 | 親ページ（`simp_all`）と同様 |
| `simp_arith` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.simpArith` | 任意 | `simp` + 算術補題 | 親ページ（`simp`）と同様 | 親ページ（`simp`）と同様 |
| `simp_arith!` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.tacticSimp_arith!_` | 任意 | `simp_arith` の積極版 | 親ページ（`simp`）と同様 | 親ページ（`simp`）と同様 |
| `simp_intro` [→詳細](detail/簡約/simp.md) | 簡約 | `Lean.Parser.Tactic.simpIntro` | ∀/→ | `simp` で簡約しながら仮定導入 | 親ページ（`simp`）と同様 | 親ページ（`simp`）と同様 |
| `simp_rw` [→詳細](detail/書換/simp_rw.md) | 書換 | `Mathlib.Tactic.simp_rw` | 等式 | 束縛子内側まで書換が届く `rw` | バインダ内部まで書き換えが届く・全出現を一括で書換 | simp より遅い・全出現が書き換わるので一部のみ変更には不向 |
| `simp_wf` | 制御 | `tacticSimp_wf` | 任意 | 停止性定義展開（4.12 以降不要） | | |
| `simpa!` [→詳細](detail/簡約/simpa.md) | 簡約 | `Lean.Parser.Tactic.tacticSimpa!_` | 任意 | `simpa` の積極版 | 親ページ（`simpa`）と同様 | 親ページ（`simpa`）と同様 |
| `simpa?` [→詳細](detail/簡約/simpa.md) | 簡約 | `Lean.Parser.Tactic.tacticSimpa?_` | 任意 | `simpa` の提案版 | 親ページ（`simpa`）と同様 | 親ページ（`simpa`）と同様 |
| `simpa?!` [→詳細](detail/簡約/simpa.md) | 簡約 | `Lean.Parser.Tactic.tacticSimpa?!_` | 任意 | `simpa?` の積極版 | 親ページ（`simpa`）と同様 | 親ページ（`simpa`）と同様 |
| `sizeOf_list_dec` | 特化 | `List.tacticSizeOf_list_dec` | 線形算術 | `a ∈ as` から sizeOf 証明 | | |
| `skip` [→詳細](detail/制御/skip.md) | 制御 | `Lean.Parser.Tactic.skip` | 任意 | 何もしない（no-op） | 常に成功する no-op・条件分岐の穴埋めや repeat の終端に利用 | ゴールを一切閉じない・sorry と異なりエラーも出ない |
| `sleep` | デバッグ | `Lean.Parser.Tactic.sleep` | 任意 | 指定ミリ秒停止（デバッグ専用） | | |
| `sleep_heartbeats` | デバッグ | `tacticSleep_heartbeats_` | 任意 | n ハートビート待機（デバッグ用） | | |
| `slice_lhs` | 特化 | `Mathlib.Tactic.Slice.sliceLHS` | 等式 | 圏論等式の左辺に conv ズーム | | |
| `slice_rhs` | 特化 | `Mathlib.Tactic.Slice.sliceRHS` | 等式 | 圏論等式の右辺に conv ズーム | | |
| `smul_tac` | 特化 | `RatFunc.tacticSmul_tac` | 等式 | `K⟮X⟯` 等式を `induction_on` で解く | | |
| `solve` [→詳細](detail/制御/solve.md) | 制御 | `Lean.solveTactic` | 任意 | 完全解決時のみ成功する `first` | 完全解決のみ成功・部分進捗を防ぐ安全装置 | 段階的処理には使えない |
| `solve_by_elim` [→詳細](detail/自動化/solve_by_elim.md) | 自動化 | `Lean.Parser.Tactic.solveByElim` | 仮定依存 | 仮定+補題で前向き・後ろ向き推論 | 仮定のチェーンで推論を自動構成シaesop より軽量 | 探索深度制限ありシsimp/rw は行わない |
| `sorry_if_sorry` | デバッグ | `CategoryTheory.sorryIfSorry` | 任意 | ゴール型に `sorry` 含む場合のみ sorry | | |
| `specialize_all` | 補題適用 | `Mathlib.Tactic.TautoSet.specialize_all` | 仮定依存 | 全仮定に `specialize` 適用 | | |
| `split_ands` [→詳細](detail/導入/split_ands.md) | 導入 | `Batteries.Tactic.tacticSplit_ands` | ∧ | `And.intro` を繰り返し | ∧ ゴールを constructor で繰り返し分割・複数 And に対応 | ∧ のみ対象で Or 等の型は処理しない |
| `split_ifs` [→詳細](detail/分解/split_ifs.md) | 分解 | `Lean.Parser.Tactic.splitIfs` | Decidable | 全 `if-then-else` を展開 | ネストした if を一括展開・条件が各ケースの仮定に自動追加 | if が多いと 2^n サブゴール爆発 |
| `squeeze_scope` | 簡約 | `Mathlib.Tactic.squeeze_scope` | 任意 | simp 補題リストのスコープ表示 | | |
| `stop` | デバッグ | `Lean.Parser.Tactic.tacticStop_` | 任意 | `repeat sorry` の糖衣構文 | | |
| `subsingleton` [→詳細](detail/閉鎖/subsingleton.md) | 閉鎖 | `Mathlib.Tactic.subsingletonStx` | 等式 | Subsingleton で等式証明 | Subsingleton 型の等式を自動証明・証明項の一意性を利用 | Subsingleton インスタンスがないと失敗 |
| `subst_eqs` [→詳細](detail/変換/subst_eqs.md) | 変換 | `Lean.Parser.Tactic.substEqs` | 仮定依存 | 全等式仮定に `subst` | コンテキスト内の全等式仮定に subst を一括適用 | 変数が lhs でない等式は無視される・手動 subst が必要な場合あり |
| `subst_hom_lift` | 特化 | `CategoryTheory.tacticSubst_hom_lift___` | 仮定依存 | 圏論 `IsHomLift` で射を置換 | | |
| `subst_vars` [→詳細](detail/変換/subst_vars.md) | 変換 | `Lean.Parser.Tactic.substVars` | 仮定依存 | 全 `x = t` / `t = x` 仮定に `subst` | 変数を含む全等式仮定を一括消去・コンテキスト整理に有用 | 変数でない等式には適用されない |
| `substs` [→詳細](detail/変換/substs.md) | 変換 | `Mathlib.Tactic.Substs.substs` | 仮定依存 | 仮定リストに順番に `subst` | 指定した仮定リストに順番に subst を適用 | 消去順序の制御が困難・依存関係に注意 |
| `success_if_fail_with_msg` | デバッグ | `Mathlib.Tactic.successIfFailWithMsg` | 任意 | 指定メッセージ失敗時のみ成功（テスト用） | | |
| `suggestions` | 探索 | `Lean.Parser.Tactic.suggestions` | 任意 | ライブラリ提案エンジンで定理表示 | | |
| `swap` [→詳細](detail/制御/swap.md) | 制御 | `Batteries.Tactic.tacticSwap` | 任意 | `pick_goal 2`（1番↔2番入替） | 先頭 2 つのゴールを入れ替え・pick_goal 2 の別名 | ゴールが 1 つだけの場合は無意味・on_goal の方が明確 |
| `swap_var` [→詳細](detail/変換/swap_var.md) | 変換 | `Mathlib.Tactic.swapVar` | 任意 | 2変数名入れ替え | 2 つの変数名を仮定・ゴール全体で入れ替え | 型が異なる変数の場合は失敗する可能性あり |
| `symm_saturate` | 変換 | `Mathlib.Tactic.symmSaturate` | 等式 | 対称性で得られる等式を全追加 | | |

---

### t

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `tauto_set` [→詳細](detail/自動化/tauto_set.md) | 自動化 | `Mathlib.Tactic.TautoSet.tauto_set` | 任意 | 集合等式・包含を命題論理的に解く | 集合の等式・包含を命題論理的に完全解決・ext + tauto 相当 | 量化子が絡む集合論的命題には失敗 |
| `tfae` [→詳細](detail/特化/tfae.md) | 特化 | `Mathlib.Tactic.TFAE` | 任意 | TFAE（以下全同値）フレームワーク | 同値条件列挙証明が自然な形で記述可能・最小含意関係のみで OK | TFAE 型ゴールでないと不可・含意のチェーンが不完全なら失敗 |
| `tfae_finish` [→詳細](detail/特化/tfae_finish.md) | 特化 | `Mathlib.Tactic.TFAE.tfaeFinish` | 任意 | TFAE 証明の仕上げ | TFAE ゴールを含意仮定から自動完成させる | 各含意が揃っていないと失敗 |
| `tfae_have` [→詳細](detail/特化/tfae_have.md) | 特化 | `Mathlib.Tactic.TFAE.tfaeHave` | 任意 | TFAE に `Pᵢ → Pⱼ` 仮定追加 | TFAE リストに含意仮定を段階的に追加・柔軟な証明構成 | TFAE 型のゴールでないと使えない |
| `toFinite_tac` | 特化 | `Set.tacticToFinite_tac` | 任意 | `Set.Finite` の autoParam | | |
| `to_encard_tac` | 特化 | `Set.tacticTo_encard_tac` | 任意 | `card` → `encard` 変換 | | |
| `trace` [→詳細](detail/デバッグ/trace.md) | デバッグ | `Lean.Parser.Tactic.trace` | 任意 | トレースメッセージ表示 | 証明中に任意メッセージを表示・動作確認に有用 | デバッグ専用・証明を進展させない・最終証明前に削除すること |
| `trace_state` [→詳細](detail/デバッグ/trace_state.md) | デバッグ | `Lean.Parser.Tactic.traceState` | 任意 | 証明状態を Info ビューに表示 | 証明状態をログに残して複雑タクティク列のデバッグに有用 | Infoview で十分なことが多いシCI でログが冒長 |
| `trans` [→詳細](detail/変換/trans.md) | 変換 | `Batteries.Tactic.tacticTrans___` | 等式/任意 | 推移律で中間項を挿入 | 短い推移律適用に有用・= 以外の @[trans] 関係にも使える | 中間項省略でユニフィケーション失敗・3段以上は calc が推奨 |
| `transitivity` [→詳細](detail/変換/transitivity.md) | 変換 | `Batteries.Tactic.tacticTransitivity___` | 等式/任意 | `trans` の別名 | trans の別名・推移律で中間項を挿入 | 2 つ以上の推移律適用には calc が推奨 |
| `triv` | 閉鎖 | `Batteries.Tactic.triv` | 任意 | （非推奨）`trivial` の旧称 | | |
| `try` [→詳細](detail/制御/try.md) | 制御 | `Lean.Parser.Tactic.tacticTry_` | 任意 | 失敗しても成功扱い | オートメーション列での安全な挿入シrepeat と相性良好 | 失敗が隐蔽されてデバッグが困難 |
| `try?` [→詳細](detail/探索/try_question.md) | 探索 | `Lean.Parser.Tactic.tryTrace` | 任意 | 登録タクティクを試して提案 | core のみで利用可・提案をそのまま証明に貼り付け可能 | 全試行で遅い・最終証明では提案結果に置き換えること |
| `try_suggestions` | 制御 | `Lean.Parser.Tactic.tryResult` | 任意 | `try?` 内部帯補助 | | |
| `try_this` | 制御 | `Mathlib.Tactic.tacticTry_this__` | 任意 | `Try this` 提案実行 | | |
| `type_check` [→詳細](detail/デバッグ/type_check.md) | デバッグ | `tacticType_check_` | 任意 | 式の型チェック表示 | タクティクブロック内で式の型確認が可能 | デバッグ専用シInfoview ホバーで確認可能な場合が多い |

---

### u・v・w・z

| 名称 | カテゴリ | 定義元 | ゴールパターン | 概要 | Pros | Cons |
|---|---|---|---|---|---|---|
| `unfold?` | 簡約 | `Lean.Parser.Tactic.unfoldTrace` | 任意 | 展開可能な定義を提案 | | |
| `unfold_projs` [→詳細](detail/簡約/unfold_projs.md) | 簡約 | `Mathlib.Tactic.unfoldProjsStx` | 任意 | 型クラスインスタンスの射影展開 | 型クラスインスタンスの射影を展開・変換系タクティクの前処理に | 展開後の式が複雑になる場合あり |
| `unhygienic` [→詳細](detail/制御/unhygienic.md) | 制御 | `Lean.Parser.Tactic.tacticUnhygienic_` | 任意 | 衛生チェック無効化 | 衛生チェックを無効化・マクロ内変数の強制アクセスが可能 | 名前衝突のリスク・原則使用を避けること |
| `uniqueDiffWithinAt_Ici_Iic_univ` | 特化 | `Real.tacticUniqueDiffWithinAt_Ici_Iic_univ` | 任意 | `ℝ` 一意微分可能性補助 | | |
| `unit_interval` | 特化 | `unitInterval` | 線形算術 | 単位区間 `[0,1]` 自動証明 | | |
| `unreachable!` | デバッグ | `Batteries.Tactic.unreachable` | 任意 | コンパイル時パニック | | |
| `use!` [→詳細](detail/導入/use.md) | 導入 | `Mathlib.Tactic.«tacticUse!___,,»` | ∃ | `use` の再帰コンストラクタ版 | 親ページ（`use`）と同様 | 親ページ（`use`）と同様 |
| `use_discharger` [→詳細](detail/導入/use.md) | 導入 | `Mathlib.Tactic.tacticUse_discharger` | 任意 | `use` の自動ディスチャージャー | 親ページ（`use`）と同様 | 親ページ（`use`）と同様 |
| `use_finite_instance` | 特化 | `tacticUse_finite_instance` | 任意 | `Set.Finite` を `toFinite` で解く | | |
| `valid` | 特化 | `CategoryTheory.ComposableArrows.tacticValid` | 線形算術 | 合成可能射列整合性を `omega` で証明 | | |
| `volume_tac` | 特化 | `MeasureTheory.tacticVolume_tac` | 任意 | `volume` 測度合成 autoParam | | |
| `wait_for_unblock_async` | デバッグ | `Lean.Server.Test.Cancel.tacticWait_for_unblock_async` | 任意 | 非同期キャンセルテスト用内部 | | |
| `whnf` [→詳細](detail/簡約/whnf.md) | 簡約 | `Mathlib.Tactic.tacticWhnf__` | 任意 | 弱頭部正規形に変換 | 最外層のみ簡約で軽量・ラムダβ簡約等に有効 | 内部は簡約されないシWHNF の概念把握が必要 |
| `whisker_simps` | 特化 | `Mathlib.Tactic.BicategoryCoherence.whisker_simps` | 等式 | 二圏 whisker 演算の正規形 simp | | |
| `with_panel_widgets` | 制御 | `ProofWidgets.withPanelWidgetsTacticStx` | 任意 | ウィジェットパネル表示 | | |
| `with_reducible` [→詳細](detail/制御/with_reducible.md) | 制御 | `Lean.Parser.Tactic.withReducible` | 任意 | `[reducible]` のみ展開する透明度設定 | reducible 透明度のみで実行・最も軽量な展開設定 | 範囲が狭すぎて多くのタクティクが失敗する |
| `with_reducible_and_instances` [→詳細](detail/制御/with_reducible_and_instances.md) | 制御 | `Lean.Parser.Tactic.withReducibleAndInstances` | 任意 | reducible+インスタンスのみ展開 | reducible + インスタンス透明度で実行 | 展開範囲の把握が困難・default との違いを意識 |
| `with_unfolding_all` [→詳細](detail/制御/with_unfolding_all.md) | 制御 | `Lean.Parser.Tactic.withUnfoldingAll` | 任意 | opaque 以外全展開の透明度設定 | opaque 以外の全定義を展開・最も積極的な設定 | 過剰展開でパフォーマンスが大幅低下 |
| `with_unfolding_none` [→詳細](detail/制御/with_unfolding_none.md) | 制御 | `Lean.Parser.Tactic.withUnfoldingNone` | 任意 | 定義を一切展開しない透明度設定 | 定義展開なしで実行・展開による副作用を完全排除 | ほとんどのタクティクが失敗・非常に限定的なユースケース |
| `witt_truncateFun_tac` | 特化 | `witt_truncateFun_tac` | 等式 | ウィットベクトル `truncateFun` 環交換 | | |
| `wlog` [→詳細](detail/変換/wlog.md) | 変換 | `Mathlib.Tactic.wlog` | 任意 | WLOG で仮定追加 + ¬P 帰着 | 対称性を利用して証明を半減・数学の WLOG に直接対応 | using による対称性指定が不正確だと対称ゴールが閉じない |
| `wlog!` [→詳細](detail/変換/wlog.md) | 変換 | `Mathlib.Tactic.wlog!` | 任意 | `wlog` の変種 | 親ページ（`wlog`）と同様 | 親ページ（`wlog`）と同様 |
| `zify` [→詳細](detail/鋳型/zify.md) | 鋳型 | `Mathlib.Tactic.Zify.zify` | キャスト | 自然数 → 整数ゴールに変換 | Nat 飽和減算を回避シomega/linarith との相性が抗抜 | キャスト導入でゴールが大きくなる場合がある |

---

## 注記

- **変種タクティク**（`!` 付き積極版、`?` 付き提案版、`?!` 版）は基本形の詳細ページを参照
- **モナディックタクティク群**（`m` 接頭辞）は `Std.Do.SPred` ゴール専用
- **圏論専用タクティク**（`aesop_cat`・`bicategory`・`coherence` 等）は `CategoryTheory` ライブラリ使用時のみ
- **デバッグ・テスト用**（`guard_*`・`trace_state`・`sleep` 等）は本番証明に残さない
- **`?` 付き提案タクティク**は証明探索の補助。最終証明では `only [...]` 形式に置き換える

---

## 出典・ライセンス

> 本索引は以下のドキュメントの情報に基づいて作成されています:
> - [Lean 4 公式リファレンス](https://lean-lang.org/doc/reference/latest/) — © Lean FRO, Apache-2.0 License
> - [Mathlib4 ドキュメント](https://leanprover-community.github.io/mathlib4_docs/) — © Mathlib Contributors, Apache-2.0 License
> - [seasawher/mathlib4-help](https://seasawher.github.io/mathlib4-help/) — 参照元として利用
>
> 本ファイル自体は MIT License で提供されます。
