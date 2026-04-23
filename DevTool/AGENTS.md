# DevTool — S2IL 開発ツール群（簡約版）

## 目的

DevTool は S2IL 開発を補助する Lean 製 CLI 群。

## ターゲット

- `lake exe s2il-toolkit <sub>`: S2IL 依存あり
- `lake exe s2il-diag <sub>`: S2IL 依存なし（ビルド破綻時の診断用）

## 主なサブコマンド

- toolkit: `depgraph`, `symbol-map`, `proof-stats`
- diag: `sorry-list`

## 使い分け

- S2IL が build 可能: toolkit / diag の両方
- S2IL が build 不可: diag を優先

## 保守ルール

- `Diag/` は `import S2IL` を禁止
- 新規サブコマンド追加時は CLI ディスパッチと本ファイルを同時更新

## 参考

- 全オプション: `lake exe s2il-toolkit --help`
- 詳細規約: `../AGENTS.md`
