# エージェント運用プレイブック（詳細版）

`AGENTS.md` の最上位ルールから外した詳細閾値・例外運用をここに集約する。
原則・トリガ語句は AGENTS.md 側に置き、ここでは「数字付き運用ルール」のみを扱う。

---

## 検索戦略（詳細）

### 加工操作タスクの探索プロトコル

1. 対応する facade（`S2IL/<Namespace>.lean`、例: `S2IL/Operations.lean`）の冒頭目次コメントを読む
2. facade で宣言されている公開 API シグネチャを確認する
3. 実装が必要なら facade が import している公開部品ファイル (`S2IL/<Namespace>/<Component>.lean`) を辿る
4. `Internal/` は facade / 同 namespace からのみ参照する
5. それでも未到達なら対象 namespace に絞って `grep_search`

### Explore 委譲の判断軸

機械的な数値閾値（「ファイル N 本」「シンボル M 個」）は撤廃した。Greenfield 後の Lean ソースは facade + MECE 分割で 1 ファイルあたりの責務が小さく、数で測ると過剰委譲または過小委譲のいずれかに振れる。

委譲が **有効** な状況:

- 横断的な合成要約が要る（spec + 実装 + テストの三点照合、未知 namespace の構造把握）
- 同一キーワードでの `grep_search` が空ヒット 2 回続いたとき（Explore に語彙的揺らぎを委ねる）
- session memory / context に類似の探索結果が無く、結果を要約のみ受け取れば十分なとき

委譲が **不要** な状況:

- 既知シンボルの 1〜2 行確認（`grep_search` + 短い `read_file` で済む）
- 直近のターンで context に既に取り込まれているファイルの再参照
- facade 冒頭目次だけで答えが出るとき

> 重要サブエージェント（`lean-sorry-investigator` / `lean-build-doctor`）の呼び出しは数値閾値で抑制しない。閾値は guard rail ではなく **目安** として扱う。

### 委譲テンプレート

```text
runSubagent Explore
  query: "{File}.lean の L{X}〜L{Y} 付近で {目的} を探して、行番号付きで上位 5 件を返して"
  thoroughness: quick
```

---

## ビルド後チェックリスト

### `lake build` を VS Code task で直接叩いた場合

`build.ps1` を経由しない場合は `sorry-goals.md` が更新されない。コミット前に次を実行する。

```powershell
.github/skills/lean-build/scripts/update-sorry-goals.ps1
git status   # sorry-goals.md の差分が想定通りか確認
```

`build.ps1` 経由ならこの手順は自動化されるため省略可。

---

## ファイル編集の落とし穴

### 置換失敗時

`replace_string_in_file` の失敗は「未変更」を意味しない。
失敗後は `read_file` か `grep_search` で現状を確認してから再試行する。

### 大量置換

10 件以上の独立した置換は `multi_replace_string_in_file` でバッチ化する。
連鎖編集（前の置換結果に依存する）は順次 `replace_string_in_file` で行う。

---

## 進捗報告

- 中間報告は「現在地（1 行）」と「次アクション（1 行）」のみで構成する
- 長文の探索結果やコードブロックを毎ターン繰り返さない（`Scratch/` または session memory に退避）
- 収集系ツールは目的単位でバッチ呼び出しする（`grep_search` 単発の連打を避ける）

---

## 撤退判断の閾値

| 条件 | 判定 |
|---|---|
| 同一 sorry に 8 アプローチ以上失敗 | 撤退 |
| 同一ゴール形状が戦略変更後に 2 回再出現 | 撤退検討 |
| 3 セッションまたぎで同一 sorry が未進展 | 撤退 |

詳細フロー: [proof-retreat-pivot-guide.md](proof-retreat-pivot-guide.md)。

---

## シェル運用（補足）

- PowerShell 文字列置換は `-creplace` 固定（理由: [powershell-conventions.md](powershell-conventions.md)）
- `.github/skills/` のスクリプトはシェル前置なしで直接実行する
- 非同期ビルドの状態確認は `get_terminal_output` を 1 ターン 1 回までにする（タイマーが未完了なら次ターンの自動通知を待つ）

---

## セッションメモリ運用（詳細）

- 多段作業（Wave / 証明チェーン）は最初の 3 ツール呼び出し以内に `/memories/session/` を作成する
- 1 セッション 2 ファイル以内
- 5000 トークン超のドキュメントを扱うときは要約メモを先に作り、全文の再読を避ける

詳細テンプレート: [session-memory-guide.md](session-memory-guide.md)

---

## sorry-plan.json の `axiom_delta` 規約

`recently_completed[]` の各エントリで axiom を増減させた場合は次フィールドを必ず付ける。
総数が変わらない（`net = 0`）場合でも記録する — 引き継ぎ時に「なぜ総数が変わっていないか」を再確認するコストを排除するため。

```json
"axiom_delta": {
  "removed": ["<symbol>"],
  "added": ["<bridge-axiom-symbol>"],
  "net": 0,
  "rationale": "D-10D で `Internal/Collision.lean` から theorem 化予定のブリッジ"
}
```

適用契機:

- 旧 axiom を取り下げ（反例発覚 / シグネチャ強化）
- 中間結果を意図的にブリッジ axiom として導入（後続 phase で同時解消の見込みあり）
- axiom を theorem 化（`removed` のみ、`net < 0`）
