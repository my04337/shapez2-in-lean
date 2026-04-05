---
name: lean-proof-progress
description: >
  Lean 4 の証明作業の進捗を管理し、sorry 状態のトラッキング・撤退判断・セッション間の状態復元を行う。
  Use when: proof progress, sorry status, proof stuck, review proof attempt,
  continue proof, resume proof, proof session, track sorry, retreat decision.
metadata:
  argument-hint: '証明の進捗管理と撤退判断を行います'
---

# 証明進捗管理スキル

sorry のトラッキング・撤退判断・セッション間の状態保持を行う。

## セッション開始

1. **前回の状態を確認**: `/memories/repo/`、`docs/knowledge/`、`/memories/session/`
2. **sorry 一覧を取得**:
   ```powershell
   .github/skills/lean-build/scripts/build.ps1
   Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json |
       Where-Object { $_.isSorry -eq $true } | Format-Table file, line, message
   ```
3. **依存関係を把握**: `lean-depgraph` で sorry ノードの依存を可視化
   - `lean-sorry-snapshot` サブエージェントで Steps 2+3 を一括実行可能
4. **REPL でゴール確認**（オプション）: sorry を含む定理を REPL で実行し `sorries[0].goal` を取得

## sorry 状態の記録

| 項目 | 内容 |
|---|---|
| ファイル:行 | sorry の位置 |
| 型シグネチャ | 証明すべき命題 |
| 試行した戦略 | simp, omega, induction 等 |
| 結果 | 成功 / 失敗 / 部分的進展 |
| 依存 | 他 sorry への依存 |
| 推定難易度 | 低 / 中 / 高 |

セッション終了時に `/memories/repo/` に記録する。

## 撤退判断基準

### レッドフラグ（即座に再検討）

- `cases` で到達不能ケースが `sorry` のまま残る
- 仮定を次々追加しないと進まない / `exact?` が何も見つけない
- **sorry の増殖**: 1 つ解こうとして 3 つ以上発生
- 中間補題に反例が見つかった
- ペアワイズ条件で N 要素の性質を主張 / グリーディ不変条件で第三者を無視

### イエローフラグ（注意続行）

- 同一戦略で 200 行超 / 同じエラー 3 回以上 / cases 分岐 8 つ以上

### 撤退時のアクション

1. 現状をメモリに記録（試行戦略・到達点・失敗理由）
2. `docs/knowledge/` に知見を反映（偽定理情報・証明ノウハウ）
3. 代替戦略を検討（別の分解・一般化/特殊化・Mathlib 活用）
4. 一時棚上げ（依存する他の定理を先に証明）

## sorry の優先順位

1. **独立 sorry**（他に依存しない）— 即着手可能
2. **被依存数が多い** — 連鎖的に解決される可能性
3. **推定難易度が低い** — 早期の成功体験
4. **クリティカルパス上** — プロジェクト目標に直結

## Gotchas

- sorry は `warning` として報告。`declaration uses 'sorry'` で識別
- sorry 連鎖は最小限に（偽 sorry → 連鎖破綻）
- セッションメモリは会話終了で消える → 長期情報は `/memories/repo/` へ

## 関連

**lean-proof-planning** / **lean-counterexample** / **lean-build** / **lean-depgraph**
サブエージェント: **lean-sorry-snapshot** / **lean-theorem-checker**
