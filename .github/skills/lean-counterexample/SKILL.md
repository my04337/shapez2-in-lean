---
name: lean-counterexample
description: >
  Lean 4 の定理・補題に対して体系的に反例チェックを行い、偽定理の早期発見をする。
  具体値の代入、境界値テスト、#eval / decide による機械検証を提供する。
  Use when: check counterexample, verify theorem, is this true, validate lemma,
  false theorem, counterexample search, theorem verification, check if provable.
metadata:
  argument-hint: '定理の反例チェックを体系的に行います'
---

# 反例の体系的チェック

定理や補題の真偽を、コーディング着手前に体系的な反例探索で確認する。
偽定理への投資を早期に打ち切るための防御的プロセス。

## 動機

過去の証明作業で、偽定理の早期発見が繰り返し遅れた。
`shouldProcessBefore` の非反対称性も、構造クラスタ上の反対称性も、
体系的な反例チェックを行えば早期に特性を把握できた。

## 手順

### 1. 量化変数の特定

定理のシグネチャから量化された変数を特定する。

```lean
-- 例: theorem foo (l : Layer) (q : QuarterPos) : P l q
-- 量化変数: l : Layer, q : QuarterPos
```

### 2. テストケースの列挙

変数の型ごとに境界値・退化ケースを列挙する:

| 型 | テストケース |
|---|---|
| `List α` | `[]`, `[x]`, `[x, y]` |
| `Layer` | 各方角の組み合わせ（最大 16 パターン） |
| `Shape` | 空シェイプ、1レイヤ、2レイヤ、3レイヤ |
| `QuarterPos` | `.ne`, `.nw`, `.se`, `.sw` (全4値) |
| `Nat` | `0`, `1`, `2`, 大きい値 |
| `Bool` | `true`, `false` |
| `Option α` | `none`, `some x` |

有限型は全探索が望ましい。

### 3. 機械検証

#### `#eval` による検証（計算可能な場合）

```lean
-- Bool を返す関数で検証
#eval do
    let cases := [case1, case2, case3]
    for c in cases do
        if !(checkProperty c) then
            IO.println s!"反例発見: {c}"
            return
    IO.println "全ケース通過"
```

#### `decide` による全探索（有限型の場合）

```lean
-- 有限型なら Decidable で全探索
example : ∀ q : QuarterPos, P q := by decide
```

#### テスト用スクラッチファイル

検証コードが大きい場合:

1. 一時ファイル `Test/Scratch.lean` に検証コードを書く
2. 実行:
   - **Windows**: `lake env lean Test/Scratch.lean`
   - **macOS / Linux**: `lake env lean Test/Scratch.lean`
3. エラーがなければ反例なし（探索範囲内で）

### 4. 反例発見時の対応

反例が見つかった場合:

1. **反例の最小化**: 不要な変数を除去し、最小の反例を特定
2. **定理の修正案を検討**:
   - 仮定の追加（`h : condition →` を前提に加える）
   - 結論の弱化（等式を不等式にする等）
   - 定理自体の撤回（偽なら証明しない）
3. **修正後の定理を再度反例チェック**

### 5. 反例が見つからない場合

- 「探索範囲内では反例なし」と報告
- 探索範囲の記録: どの変数でどの範囲を試したか
- 証明着手の判断材料とする（保証ではない）

## このプロジェクトでの具体例

### Shape / Layer の検証

```lean
-- Layer は Quarter × 4 の構造
-- 全 QuarterPos を列挙して検証
#eval do
    let positions : List QuarterPos := [.ne, .nw, .se, .sw]
    for p in positions do
        -- 各方角での性質を検証
        ...
```

### 操作の可換性チェック

```lean
-- rotate と cut が可換かチェック
#eval do
    let layers := generateTestLayers  -- テスト用レイヤ一覧
    for l in layers do
        if rotate (cut l) ≠ cut (rotate l) then
            IO.println s!"反例: {l}"
```

### N 要素の相互作用チェック（3-cycle 検出パターン）

ペアワイズな性質（2 要素間の反例チェック）だけでは不十分なことがある。
**3 要素以上の相互作用** も体系的にチェックすべき。

典型パターン: 2-cycle 禁止だが 3-cycle が存在する場合

```lean
-- shouldProcessBefore の 3-cycle 検出
-- ペアワイズな 2-cycle チェックでは見逃す
#eval do
    let units := [a, b, w]  -- テスト用 FallingUnit
    -- 全順列で sortFallingUnits の結果を検証
    for perm in units.permutations do
        let sorted := sortFallingUnits perm
        -- 期待される順序と比較
        ...
```

**教訓 (2026-06 sortFU_preserves_spb_order)**:
- 定理の仮定が「ペアワイズ」の条件しか要求しない場合、3 要素以上の組み合わせで反例が出る
- グリーディアルゴリズム（最初のマッチで停止する）の定理では、
  第三者が処理を遮るケースを必ずチェックする
- 反例: `l = [w, a, b]` where spb: a→b→w→a (3-cycle) → insertSorted が期待通り動かない

## Gotchas

- `#eval` は `Decidable` でない `Prop` には使えない。`Bool` 値を返す関数に変換する
- `BEq` と `DecidableEq` は異なる。`BEq` は計算的等価性、`DecidableEq` は命題的等価性
- 全探索は型のカーディナリティが大きいと実用的でない。
  `Layer` は 4方角 × 各方角の取り得る値なので、現実的な範囲で抽出する
- `sorry` を含むコードの `#eval` 結果は信頼できない

## 関連スキル

- **lean-proof-planning**: 反例チェックを含む証明戦略の全体フロー
- **lean-proof-progress**: 反例チャックの結果を進捗管理に反映
