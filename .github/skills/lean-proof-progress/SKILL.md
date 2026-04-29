---
name: lean-proof-progress
description: >
  Long-term proof progress / retreat decision reference: sorry tracking, session boundary memory,
  pivot triggers (3 sessions / 8 approaches / counterexample found).
  Use when: proof progress, sorry status, proof stuck, review proof attempt,
  continue proof, retreat decision, pivot decision,
  証明進捗, 撤退判断, pivot 判断, sorry トラッキング.
  Returns: long-term tracking conventions + retreat criteria.
  Don't call when: you need a one-shot session restart (use agent `lean-session-restorer`).
metadata:
  argument-hint: 'Reference: long-term proof progress and retreat criteria'
---

# 証明進捗管理スキル

sorry のトラッキング・撤退判断・セッション間の状態保持を行う。

## セッション開始

> **自動復元**: セッション再開時は **lean-session-restorer** エージェントで
> 前回との差分比較・ビルド状況・着手推奨までを一括実行できる（内部で lean-build-doctor と lean-sorry-investigator を委任）。

1. **前回の状態を確認**: `/memories/repo/`、`docs/s2il/`、`/memories/session/`
2. **証明計画で対象を特定**: [`docs/plans/README.md`](../../../docs/plans/README.md) を入口にして、現在のタスクに対応する計画資料を確認:
   - 関連する計画があれば、その要点と適用範囲を確認する
   - 個別計画は流動的なため、内容はビルド結果や現行コードと突き合わせる
   - シンボル検索は対応する facade (`S2IL/<Namespace>.lean`) の冒頭目次 → `grep_search` の順
3. **sorry 一覧を取得**:
   ```powershell
   .github/skills/lean-build/scripts/build.ps1
   Get-Content .lake/build-diagnostics.jsonl | ConvertFrom-Json |
       Where-Object { $_.isSorry -eq $true } | Format-Table file, line, message
   ```
4. **依存関係を把握**: `S2IL/_agent/sorry-plan.json` の `sorrys[].depends_on` を参照
   - `lean-build-doctor` エージェントで sorry 一覧と依存分類を一括取得可能
5. **REPL でゴール確認**（オプション）: sorry を含む定理を REPL で実行し `sorries[0].goal` を取得

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
- **同一ゴール状態の再出現**: 戦略変更後に sorry のゴールが以前と同一の形に戻った場合、進捗なしと判定して**即座に戦略変更**する。2 回再出現したら撤退を検討

### イエローフラグ（注意続行）

- 同一戦略で 200 行超 / 同じエラー 3 回以上 / cases 分岐 8 つ以上

### 撤退時のアクション

1. 現状をメモリに記録（試行戦略・到達点・失敗理由）
2. `docs/s2il/` に知見を反映（偽定理情報・証明ノウハウ）
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
- **Scratch クリーンアップ**: 証明・検証が完了したタイミングで、自セッションの `Scratch/commands-<sessionId>-*.jsonl` を削除する。他セッションのファイル（自分の sessionId を含まないもの）は削除しない

## 関連

**lean-proof-planning** / **lean-counterexample** / **lean-build**
ツール: **s2il-diag**（sorry-list）
エージェント: **lean-build-doctor**（ビルド + sorry インベントリ + エラー修正候補） / **lean-sorry-investigator**（1 件の sorry 調査） / **lean-session-restorer**（セッション再開）
