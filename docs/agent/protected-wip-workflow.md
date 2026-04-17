# protected WIP ワークフロー — REPL 対応スコープ管理

REPL は `import S2IL` した別モジュールとして動作するため、`private` 定義にはアクセスできない。
証明作業中は `protected` + `-- [WIP]` タグで一時的に REPL からアクセスできるようにし、完了後に `private` へ戻す。

---

## スコープ使い分けクイックリファレンス

| 修飾子 | 意味 | REPL アクセス | 識別 |
|---|---|---|---|
| `private` | ファイル内部専用。証明済み・安定 | ❌ | — |
| `protected` (意図的) | FQN 半公開。他定理から `@Ns.name` で参照される | ✅ FQN 必須 | `-- [WIP]` タグなし |
| `protected` (WIP) | 証明作業中の一時公開 | ✅ FQN 必須 | `-- [WIP]` タグあり |
| なし (public) | 外部公開 API | ✅ | doc コメント必須 |

**見分け方**: `-- [WIP]` コメントがある → WIP 一時公開（クリーンアップ対象）。なし → 意図的半公開（変更しない）。

---

## WIP フロー（フロー A: sorry あり・フロー B: 大規模見直し）

フロー A（新規証明）・フロー B（既存 `private` の一時昇格）とも同じ手順を使う。

### Step 1: `protected` + `-- [WIP]` で定義する

```lean
-- [WIP]
/-- 補題の説明 -/
protected theorem helperLemma : P := by
  sorry
```

- 名前は変えない。`-- [WIP]` が一時性の唯一のマーカー
- REPL からは必ず FQN で参照: `#check @Gravity.helperLemma`
- `open` では展開されないため、短縮名でのアクセスは不可
- **同一 namespace 内の呼び出し箇所も FQN（`Namespace.name`）に更新する**（`protected` は同一 namespace 内でも short name を無効にする）

### Step 2: クリーンアップ（証明チェーン完了・見直し完了後）

```lean
-- WIP タグを削除し protected → private に戻す
/-- 補題の説明 -/
private theorem helperLemma : P := by
  <実際の証明>
```

- Step 1 で FQN に変更した同ファイル内の呼び出し箇所を short name に戻す
- `Test/` 等の別ファイルから FQN 参照していた場合はビルドエラーになる → 要確認

---

## クリーンアップチェックリスト

```powershell
# 未クリーンアップの WIP 定理を検索
grep_search: query = "-- [WIP]"
```

- [ ] `-- [WIP]` タグを持つ `protected` を列挙する
- [ ] `-- [WIP]` コメントを削除する
- [ ] `protected` → `private` に変更する
- [ ] 別ファイルからの FQN 参照がないか確認する
- [ ] `lake build` で `errors = 0` を確認する
- [ ] コミット（コードと同一コミットに含める）
