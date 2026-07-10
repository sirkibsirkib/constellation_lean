def map_snd {A B B₂} (f: B → B₂): A × B → A × B₂
  | (a, b) => (a, f b)


#print List

example: List Nat := List.nil
example: List Nat := []
example: List Nat := List.cons 0 []
example: List Nat := List.cons 0 (List.cons 1 [])
example: List Nat := List.cons 0 (1 :: [])
example: List Nat := 0 :: (1 :: [])
example: List Nat := 0 :: 1 :: []
example: List Nat := [0,1]

def pop_where {A} (f: A → Bool): List A → Option A × List A
  | [] => (none, [])
  | a :: tail => if f a
      then (some a, tail)
      else map_snd (a :: ·) (pop_where f tail)

example: pop_where (· > 2) [1,2,3] = (some 3, [1,2]) := rfl
example: pop_where (· > 5) [1,2,3] = (none, [1,2,3]) := rfl
example: pop_where (· = 2) [1,2,3] = (some 2, [1,3]) := rfl
example: pop_where (· ≠ 2) [1,2,3] = (some 1, [2,3]) := rfl
example: pop_where (· ≠ 2) [2,2,2] = (none, [2,2,2]) := rfl

theorem pop_where_true_some_nempty {A}:
  ∀ f (l l': List A) a,
    pop_where f l = (some a, l') →
    l ≠ [] := by
  intros f l l' a Heq
  intros Habsurd
  unfold pop_where at Heq
  rw [Habsurd] at Heq
  cases Heq

theorem pop_where_nil_nil {A}:
  ∀ f (o: Option A × List A),
    pop_where f [] = o →
    (none, []) = o := by
  intros f o H
  unfold pop_where at H
  assumption

theorem pop_where_some_splits {A}:
  ∀ (f: A → Bool) (l l': List A) a,
    pop_where f l = (some a, l') →
    ∃ (l₁ l₂ : List A),
      l = l₁ ++ [a] ++ l₂ ∧ l' = l₁ ++ l₂ := by
  intro f l
  induction l
  case nil =>
    -- absurd case of `pop_where f [] = (some _, _)`
    intro l' a
    simp [pop_where]
  case cons x t Hi =>
    -- nonempty input list
    intro l' a H
    rw [pop_where] at H
    -- cases of whether head of list satisfies `f`
    by_cases Hfx : f x
    · case pos =>
      -- The head is popped by `pop_where`
      rw [Hfx] at H
      clear Hfx
      simp at H
      obtain ⟨Ha, Hb⟩ := H
      subst Ha Hb
      simp
      -- goal: pick l₁ and l₂ s.t.
      -- `x :: t = l₁ ++ x :: l₂ ∧ t = l₁ ++ l₂`
      exists []
      exists t
    · case neg =>
      -- `a` comes from the tail.

      -- drill down into `else` case in `H`
      simp at Hfx
      rw [Hfx] at H
      clear Hfx
      simp at H
      simp only [map_snd] at H
      injection H with Ha Hb

      -- reformulate `Ha`
      have Ht : pop_where f t = (some a, (pop_where f t).2) := by
        rw [← Ha]

      -- fill in premises of inductive hypothesis `Hi`,
      -- obtain lists `l₁` and `l₂` and split the conjunction.
      obtain ⟨l₁, l₂, ⟨Hl, Hl2⟩⟩ := Hi _ _ Ht

      -- fix the left and right lists in terms of `l₁` and `l₂`.
      exists x :: l₁
      exists l₂
      simp
      apply And.intro
      . subst t
        simp
      . rw [← Hb, Hl2]


theorem pop_where_some_dec_length {A}:
  ∀ (f: A → Bool) (l l': List A) a,
    pop_where f l = (some a, l') →
    l.length = l'.length + 1 := by
  intro f l l' a H
  have ⟨l₁, l₂, Ha, Hb⟩ := pop_where_some_splits _ _ _ _ H
  subst Ha Hb
  clear H
  simp
  exact rfl

theorem pop_where_some_lt_length {A}:
  ∀ (f: A → Bool) (l l': List A) a,
    pop_where f l = (some a, l') →
    l'.length < l.length := by
  intro f l l' a H
  rw [pop_where_some_dec_length _ _ _ _ H]
  apply Nat.lt_succ_self _

theorem pop_where_none_pres {A}:
  ∀ (f: A → Bool) (l l': List A),
    pop_where f l = (none, l') →
    l' = l := by
  intro f l
  induction l
  . case nil =>
    intro l' H
    simp [pop_where] at H
    assumption
  . case cons h t Hi =>
    intro l' H
    rw [pop_where] at H
    by_cases Hfh : f h
    · rw [Hfh] at H
      simp at H
    · simp at Hfh
      rw [Hfh] at H
      simp only [map_snd] at H
      injection H with Ha Hb
      have Ht : pop_where f t = (none, (pop_where f t).2) := by
        rw [← Ha]
      have Heq := Hi _ Ht
      rw [← Hb, Heq]

theorem pop_where_in {A}:
  ∀ (f: A → Bool) (l l': List A) a,
    pop_where f l = (some a, l') →
    a ∈ l := by
  intro f l l' a H
  have ⟨l₁, l₂, h, h'⟩ := pop_where_some_splits f l l' a H
  subst l
  clear H
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_cons_self
