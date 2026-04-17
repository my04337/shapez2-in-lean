---
name: lean-error-fixer
description: >
  Classify Lean 4 build errors and generate REPL-verified fixes.
  Use when: fix build error, resolve type mismatch, unknown identifier fix,
  unsolved goals fix, auto fix, error resolution, build error repair.
metadata:
  argument-hint: 'Describe the build error (or omit to auto-diagnose)'
---

# エラー自動修正スキル

ビルドエラーを分類し、REPL で修正候補を生成・検証する。
ルーティング判断は **lean-diagnostics** スキルに、ゴール分析は **lean-goal-advisor** エージェントに委ねる。

> **前提**: ビルド済みで `.lake/build-diagnostics.jsonl` が存在すること。
> 未ビルドの場合は先に `lean-build` スキルでビルドする。

---

## Step 1: エラー抽出

```powershell
# Windows
$sid = if (Test-Path .lake/session-id.tmp) { (Get-Content .lake/session-id.tmp -Raw).Trim() } else { $null }
$diagFile = if ($sid -and (Test-Path ".lake/build-diagnostics-$sid.jsonl")) { ".lake/build-diagnostics-$sid.jsonl" } else { ".lake/build-diagnostics.jsonl" }
$errors = Get-Content $diagFile | ConvertFrom-Json | Where-Object { $_.severity -eq "error" }
$errors | Select-Object file, line, message | Format-Table -AutoSize
```

```bash
# macOS / Linux
SID=$(cat .lake/session-id.tmp 2>/dev/null | tr -d '[:space:]')
DIAG_FILE=".lake/build-diagnostics.jsonl"
[ -n "$SID" ] && [ -f ".lake/build-diagnostics-$SID.jsonl" ] && DIAG_FILE=".lake/build-diagnostics-$SID.jsonl"
grep '"severity":"error"' "$DIAG_FILE" | jq '{file, line, message}'
```

---

## Step 2: エラー分類とアクション選択

エラーメッセージのパターンからアクションを自動選択する。

| パターン | 分類 | アクション |
|---|---|---|
| `unknown identifier '...'` | ID不明 | Step 3a: REPL `#loogle` / `#leansearch` で検索 |
| `unknown constant '...'` | 定数不明 | `grep_search` で定義箇所検索 → `import` 追加 |
| `type mismatch` | 型不一致 | Step 3b: REPL `#check` で型確認 → キャスト試行 |
| `application type mismatch` | 適用型不一致 | Step 3b: 同上 |
| `Function expected at <補題名>` | 補題を関数適用で使用（引数過多） | Step 3e: REPL `#check @<補題名>` で正しいシグネチャ確認 |
| `unsolved goals` | ゴール未解決 | Step 3c: **lean-goal-advisor** に委譲 |
| `declaration uses 'sorry'` | sorry | エラーではない。**lean-proof-planning** に委譲 |
| `maximum recursion depth` | 停止性 | `termination_by` / `decreasing_by` を追加 |
| 複数エラーが連鎖 | カスケード | Step 3d: Sorrifier パターン |

---

## Step 3: 修正候補の生成

### 3a: `unknown identifier` / `unknown constant`

```jsonl
{"cmd": "#loogle \"<識別子に関連する型パターン>\"", "env": 0}

{"cmd": "#leansearch \"<識別子の意図を英語で>.\"", "env": 0}
```

結果から候補名を取得し、`#check` で確認。import パスが分かればファイル先頭に `import` を追加。

### 3b: `type mismatch` / `application type mismatch`

```jsonl
{"cmd": "#check <問題の式>", "env": 0}

{"cmd": "#check <期待される型>", "env": 0}
```

型の差分から変換候補を選択:

| 型の差分 | 修正候補 |
|---|---|
| `Nat` ↔ `Int` | `Int.ofNat` / `.toNat` / `norm_cast` |
| `Fin n` ↔ `Nat` | `Fin.val` / `⟨_, proof⟩` |
| `↑x` が不一致 | `push_cast` / `norm_cast` |
| 暗黙引数の推論失敗 | `@` で明示適用 |

### 3c: `unsolved goals`

ゴール状態を REPL で取得し、**lean-goal-advisor** エージェントに委譲するか、
`lean-tactic-select` スキルのマップから第1候補タクティクを試行する。

### 3d: Sorrifier パターン（カスケードエラー）

複数エラーが連鎖している場合、**最内側の `have` ブロック** から 1 箇所ずつ `sorry` 化して再ビルドする。
1 置換ごとに再コンパイルし、カスケードエラーを除去してから個別に取り組む。

### 3e: `Function expected at <名前>` — 補題シグネチャの確認

Lean が「関数が期待されるが項が与えられた」と報告する場合、その補題を引数付きで呼んでいるが
実際は引数なしの命題型（`Prop`）であることが多い。

```jsonl
{"cmd": "#check @beq_iff_eq", "env": 0}
{"cmd": "#check @<問題の補題名>", "env": 0}
```

- `.mpr` / `.mp` で Iff を展開してから適用するか、`apply`/`exact` で引数を除去する
- `beq_iff_eq` は `(a == b) = true ↔ a = b` という型で、引数を与えない形で使う



## Step 4: 修正候補の検証

修正コードを REPL で実行し、エラーが解消されることを確認する。

```jsonl
{"cmd": "<修正版コード>", "env": 0}
```

- `messages` にエラーなし → **修正成功**
- 別のエラー発生 → Step 2 に戻る（最大 3 回リトライ）

---

## 出力フォーマット

### エラー修正レポート

| # | ファイル:行 | 分類 | 修正内容 | 検証 |
|---|---|---|---|---|
| 1 | `S2IL/Foo.lean:42` | `unknown identifier` | `import Mathlib.Data.List.Basic` 追加 | ✅ |
| 2 | `S2IL/Bar.lean:10` | `type mismatch` | `norm_cast` を追加 | ✅ |
| 3 | `S2IL/Baz.lean:55` | `unsolved goals` | → lean-goal-advisor に委譲 | — |

---

## Gotchas

- `declaration uses 'sorry'` は error ではなく warning。このスキルの対象外
- カスケードエラーは 1 箇所の修正で複数消えることがある。最内側から修正する
- REPL で検証しても本体ビルドで再現するとは限らない（import の違い等）。最終確認は `lean-build` で行う
- `unknown identifier` は Mathlib バージョンアップによる名前変更が原因のことが多い

## 関連

- **スキル**: `lean-diagnostics`（エラー分類の詳細ガイド・ルーティングフロー）
- **スキル**: `lean-repl`（REPL 実行の詳細）
- **エージェント**: `lean-goal-advisor`（unsolved goals の修正）
- **エージェント**: `lean-lemma-finder`（unknown identifier の補題検索）
