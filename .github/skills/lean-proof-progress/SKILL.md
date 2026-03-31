---
name: lean-proof-progress
description: >
  Lean 4 の証明作業の進捗を管理し、sorry 状態のトラッキング・撤退判断・セッション間の状態復元を行う。
  Use when: proof progress, sorry status, proof stuck, review proof attempt,
  continue proof, resume proof, proof session, track sorry, retreat decision.
metadata:
  argument-hint: '証明の進捗管理と撤退判断を行います'
---

# 証明の進捗管理と撤退判断

証明作業のセッション間での状態保持、sorry の依存トラッキング、
および撤退判断の基準を提供する。

## 動機

1 つの sorry に対して複数セッションにわたる堂々巡りが発生した。
「いつ戦略を変えるか」「いつ一時撤退するか」の判断基準がなかった。

## セッション開始時の手順

### 1. 前回の状態を復元

以下のソースから前回の証明状態を確認する:

1. **`/memories/repo/`**: リポジトリメモリに保存された証明状態
2. **`docs/knowledge/`**: 証明に関するナレッジファイル
3. **`/memories/session/`**: セッションメモリ（現セッションのみ）

### 2. 現在の sorry 一覧を取得

**lean-build** でビルドし、JSONL 診断から sorry を抽出:

```powershell
# Windows
.github/skills/lean-build/scripts/build.ps1
Get-Content .lake/build-diagnostics.jsonl |
    ConvertFrom-Json |
    Where-Object { $_.isSorry -eq $true } |
    Format-Table file, line, message
```

```bash
# macOS / Linux
.github/skills/lean-build/scripts/build.sh
grep '"isSorry":true' .lake/build-diagnostics.jsonl | jq .
```

### 3. sorry の依存関係を把握

**lean-depgraph** で sorry を含む宣言の依存関係を可視化:

```
.github/skills/lean-depgraph/scripts/depgraph.ps1
```

sorry を含むノードは赤色で強調される。依存グラフから:
- **独立 sorry**: 他の sorry に依存しない → 即座に着手可能
- **依存 sorry**: 他の sorry の結果が必要 → 依存先を先に解決

## 進捗トラッキング

### sorry 状態の記録

各 sorry について以下を追跡する:

| 項目 | 内容 |
|---|---|
| ファイル:行 | sorry の位置 |
| 型シグネチャ | 何を証明する必要があるか |
| 試行した戦略 | `simp`, `omega`, `induction` 等 |
| 結果 | 成功 / 失敗 / 部分的進展 |
| 依存 | 他の sorry への依存 |
| 推定難易度 | 低 / 中 / 高 |

### セッション終了時の記録

セッション終了前に以下をリポジトリメモリに記録する:

1. 残存 sorry の一覧と状態
2. 試行した戦略とその結果
3. 次セッションへの申し送り事項

記録先: `/memories/repo/` に証明対象ごとのファイル

## 撤退判断基準

以下の基準に該当したら **戦略の再検討** を行う:

### レッドフラグ（即座に再検討）

- **偽定理のシグナル検出**:
  - `cases` で到達不能と期待したケースが `sorry` のまま残る
  - 仮定を次々と追加しないと進まない
  - `exact?` / `apply?` が何も見つけない（通常は何か見つかるはず）
  - **ペアワイズ条件で N 要素の性質を主張**: 3 要素以上の反例を要確認
  - **グリーディアルゴリズムの不変条件**: 第三者の影響を無視していないか
- **sorry の増殖**: 1 つの sorry を解こうとして 3 つ以上の新しい sorry が発生
- **反例チェックの失敗**: 中間補題に反例が見つかった
- **偽定理の発見**: 依存先の sorry が偽定理と判明した場合、依存する全 sorry の見直しが必要

### イエローフラグ（注意して続行）

- **行数超過**: 同一戦略で 200 行超のコードを書いている
- **堂々巡り**: 同じエラーメッセージが 3 回以上出現
- **複雑性の爆発**: `cases` 分岐が 8 つ以上に増加

### 撤退時のアクション

1. **現状をメモリに記録**: 試行した戦略・到達点・失敗理由
2. **代替戦略の検討**:
   - 別の分解方法（異なる帰納法の適用）
   - 補題の一般化 or 特殊化
   - Mathlib の既存定理の活用
3. **一時棚上げ**: 依存する他の定理を先に証明し、後で戻る

## sorry 優先順位の決定

複数の sorry がある場合、以下の優先順で着手する:

1. **独立 sorry（他に依存しない）** — 即座に着手可能
2. **被依存数が多い sorry** — 解決すると他の sorry も連鎖的に解決される可能性
3. **推定難易度が低い sorry** — 早期の成功体験で進捗を生む
4. **クリティカルパス上の sorry** — プロジェクト目標に直結

## Gotchas

- `sorry` は warning として報告されるが、`declaration uses 'sorry'` のメッセージで識別する
- sorry を含む定理を使って別の證明を進める場合、元の sorry が偽なら連鎖的に破綻する。
  sorry チェーンは最小限にする
- セッションメモリ (`/memories/session/`) は会話終了で消える。
  長期的な情報はリポジトリメモリ (`/memories/repo/`) に保存する

## 関連スキル

- **lean-proof-planning**: 証明着手前の戦略検証
- **lean-counterexample**: 偽定理疑惑時の反例チェック
- **lean-build**: ビルドによる sorry 一覧の取得
- **lean-diagnostics**: 診断情報の解析
- **lean-depgraph**: sorry 間の依存関係の可視化
