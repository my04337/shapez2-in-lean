# REPL セッション state ガイド

`Scratch/_state/{task}.json` に各証明タスクの REPL 作業状態を残すことで、
セッション再開時のゴール再現コストを削減する。

## 目的

- 再開時に REPL で `sorry` を再現 → ゴール表示 → 候補補題列挙 のラウンドを省略
- 試行済みの戦術・行き詰まり理由・成功した補題適用を累積

## フォーマット

```json
{
  "task": "waveStep_ngs_strict_bound",
  "file": "S2IL/Operations/Gravity/ProcessWave.lean",
  "line": 46,
  "last_goal": "⊢ nonGroundedLayerSum (waveStep s) + 1 ≤ nonGroundedLayerSum s",
  "useful_lemmas": [
    "landing_sum_bound",
    "placeLDGroupsLandings_mem_exists_drop_ge_one",
    "nonGroundedLayerSum_clear_add"
  ],
  "dead_ends": [
    "induction on settling.length — placeLDGroups 展開で IH 不整合",
    "direct omega — NGS 定義展開前に失敗"
  ],
  "updated": "2026-04-21",
  "notes": "waveStep_grounding_mono がボトルネック。 #5 cluster / #6 pin の landing edge 保存が未着手。"
}
```

## 運用

- REPL で有用な進展があった時点でエージェントが更新する（コミット対象）
- `transplant-proof.ps1` が `.lean` 移植成功時に該当タスクの `updated` を自動更新する（TODO）
- ファイル名は sorry のシンボル名を kebab-case せず **そのまま** 使う（Lean の declaration 名と一致）
