# DevTool — S2IL 開発ツール群（簡約版）

## 目的

DevTool は S2IL 開発を補助する Lean 製 CLI 群。

## ターゲット

- `lake exe s2il-diag <sub>`: S2IL 依存なし（ビルド破綻時の診断用）

Phase A (2026-04-24) で `s2il-toolkit` は廃止された（旧 `depgraph` / `symbol-map` / `proof-stats` サブコマンドはインデックス機構に依存していたため）。
旧ソースは `_archive/pre-greenfield/DevTool/Toolkit/` に退避済み。

## 主なサブコマンド

- diag: `sorry-list`

## 使い分け

S2IL のビルド状況によらず `s2il-diag` が使える。

## 保守ルール

- `Diag/` は `import S2IL` を禁止
- 新規サブコマンド追加時は CLI ディスパッチと本ファイルを同時更新

## 参考

- 全オプション: `lake exe s2il-diag --help`
- 詳細規約: `../AGENTS.md`
