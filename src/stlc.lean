import dict
import tactic
import tactic.induction

def var := ℕ 

set_option pp.generalized_field_notation false

inductive Typ : Type
| Lam : Typ -> Typ -> Typ
| Nat : Typ
| Unit : Typ

notation t1 ` -> ` t2 := Typ.Lam t1 t2

inductive Term : Type
| Var : var -> Term
| Lam : var -> Typ -> Term -> Term 
| Ap  : Term -> Term -> Term
| Nat : ℕ -> Term
| Plus : Term -> Term -> Term
| Unit : Term

notation `\` `(`x`:`S`)` `.` t := Term.Lam x S t
notation `()` := Term.Unit
notation `[`n`]` := Term.Nat n


inductive value : Term -> Prop
-- functions are values!
| Lam : ∀ (x : var) (τ : Typ) (e: Term), value (Term.Lam x τ e)
| Unit : value ()
| Nat : ∀ (n : ℕ), value [n]

def isVal (t : Term) := value t

def subst (s : Term) (v : var) : Term -> Term 
| (Term.Var n) := if n = v then s else (Term.Var n)
| (Term.Lam n τ e) := if v = n then 
                        Term.Lam n τ e
                      else 
                        Term.Lam n τ (subst e)
| (Term.Ap e1 e2) := Term.Ap (subst e1) (subst e2)
| Term.Unit := Term.Unit
| (Term.Nat n) := Term.Nat n
| (Term.Plus m n) := Term.Plus (subst m) (subst n)

notation `[` s `//` x `]` t := subst s x t

inductive step : Term -> Term -> Prop
| ApLam : ∀ v x τ e, value v -> step (Term.Ap (Term.Lam x τ e) v) ([v//x]e)
| Ap1 : ∀ e1 e1' e2, step e1 e1' -> step (Term.Ap e1 e2) (Term.Ap e1' e2)
| Ap2 : ∀ e1 e2 e2', step e2 e2' -> step (Term.Ap e1 e2) (Term.Ap e1 e2')
| Plus1 : ∀ e1 e1' e2, step e1 e1' -> step (Term.Plus e1 e2) (Term.Plus e1' e2)
| Plus2 : ∀ e1 e2' e2, step e2 e2' -> step (Term.Plus e1 e2) (Term.Plus e1 e2')
| PlusNat : ∀ n m, step (Term.Plus (Term.Nat n) (Term.Nat m)) (Term.Nat (n + m))

inductive free_in : var -> Term -> Prop 
| Var : ∀ x, free_in x (Term.Var x)
| Lam : ∀ x y τ e, x ≠ y -> free_in x e -> free_in x (Term.Lam y τ e)
| Ap1 : ∀ x e1 e2, free_in x e1 -> free_in x (Term.Ap e1 e2)
| Ap2 : ∀ x e1 e2, free_in x e2 -> free_in x (Term.Ap e1 e2)
| Plus1 : ∀ x e1 e2, free_in x e1 -> free_in x (Term.Plus e1 e2)
| Plus2 : ∀ x e1 e2, free_in x e2 -> free_in x (Term.Plus e1 e2)

def FV (e : Term) := {x | free_in x e}

-- this was a 15-312 assignment
inductive not_free_in : var -> Term -> Prop
| Var : ∀ x y, x ≠ y -> not_free_in x (Term.Var y)
| Ap : ∀ x e1 e2, not_free_in x e1 -> not_free_in x e2 -> not_free_in x (Term.Ap e1 e2)
| Lam1 : ∀ x y τ e, x ≠ y -> not_free_in x e -> not_free_in x (Term.Lam y τ e)
| Lam2 : ∀ x τ e, not_free_in x (Term.Lam x τ e)
| Nat : ∀ x n, not_free_in x (Term.Nat n)
| Plus : ∀ x e1 e2, not_free_in x e1 -> not_free_in x e2 -> not_free_in x (Term.Plus e1 e2)
| Unit : ∀ x, not_free_in x ()

instance : has_mem var Term := ⟨free_in⟩

infix ` ↦ `:50 := step

def Context := Dict var Typ

def ctx_Empty := @Dict.empty var Typ 

notation Γ `, ` x ` : ` τ := Dict.add Γ x τ

notation `⬝` := ctx_Empty

inductive has_type : Context -> Term -> Typ -> Prop
| Var : ∀ (Γ : Context) (x : var) (τ : Typ), Dict.get Γ x = some τ -> has_type Γ (Term.Var x) τ
| Lam : ∀ (Γ : Context) (x : var) (τ₁ τ₂ : Typ) (t₁ : Term), 
    has_type (Dict.add Γ x τ₁) t₁ τ₂ -> 
    has_type Γ (Term.Lam x τ₁ t₁) (Typ.Lam τ₁ τ₂)

| Ap : ∀ Γ τ₁ τ₂ e₁ e₂, 
    has_type Γ e₁ (Typ.Lam τ₁ τ₂) -> has_type Γ e₂ τ₁ 
    -> has_type Γ (Term.Ap e₁ e₂) τ₂
| Unit : ∀ Γ, has_type Γ Term.Unit Typ.Unit 
| Nat : ∀ Γ n, has_type Γ (Term.Nat n) Typ.Nat
| Plus : ∀ Γ e₁ e₂, has_type Γ e₁ Typ.Nat -> has_type Γ e₂ Typ.Nat -> has_type Γ (Term.Plus e₁ e₂) Typ.Nat

notation Γ ` ⊢ ` e ` : ` τ  := has_type Γ e τ

lemma fn_typ_eq  {τ₁ τ₂ τ₃ τ₄ : Typ} (h : (τ₁ → τ₂) = (τ₃ → τ₄)) : τ₁ = τ₃ ∧ τ₂ = τ₄
:=
begin 
  split,
  repeat {cases h, refl,},
end


theorem unicity {Γ : Context} {τ₁ τ₂ : Typ} {e : Term} (h1 : has_type Γ e τ₁) (h2 : has_type Γ e τ₂) : τ₁ = τ₂
:= 
begin 
  induction' h1,
  {
    cases h2 with _ _ _ h',
    rw h' at h,
    apply option.some.inj,
    exact h.symm,
  },
  {
    cases h2 with _ _ _ _ _ _ _ τ1 _ h',
    specialize ih h',
    rw ih,
  },
  {
    cases h2 with _ _ _ _ _ _ _ τ1 _ h' _ τ _ _ _ h h',
    specialize ih_h1 h,
    exact (fn_typ_eq ih_h1).2,
  },
  repeat {
    cases h2,
    refl,
  },
end

lemma CFL_Lam {τ₁ τ₂ : Typ} {e : Term} (h1: has_type ctx_Empty e (Typ.Lam τ₁ τ₂)) (h2 : value e)
  : ∃x t, e = Term.Lam x τ₁ t :=
begin 
  cases h2 with x τ e,
  {
    use [x, e],
    cases h1,
    refl,
  },
  repeat {cases h1},
end

lemma CFL_Nat  {e : Term} (h1: has_type ctx_Empty e Typ.Nat) (h : value e)
  : ∃n, e = Term.Nat n:=
begin 
  cases h,
  repeat {cases h1},
  use h_1,
end

lemma CFL_Unit  {e : Term} (h1: has_type ctx_Empty e Typ.Unit) (h : value e)
  : e = Term.Unit  :=
begin
  cases h,
  cases h1,
  refl,
  cases h1,
end


theorem progress (e : Term) (τ : Typ) (h : has_type ctx_Empty e τ) : value e ∨ ∃ e', e ↦ e' :=
begin 
  induction' h with foo x τ h _ x τ τ₁ _ _ _ _ _ _ e1 e2 h h1 e1_ih e2_ih _ _ _ _ e1 e2 h1 h2,
  { contradiction },
  { exact or.inl (value.Lam x τ e) },
  {
    right,
    cases e1_ih,
    cases e2_ih,
    {
      rcases (CFL_Lam h e1_ih) with ⟨x, e, h_e1⟩,
      use ([e2 // x]e),
      rw h_e1,
      exact step.ApLam e2 x τ₁ e e2_ih,
    },
    {
      cases e2_ih with e2' e2_ih,
      use Term.Ap e1 e2',
      exact step.Ap2 e1 e2 e2' e2_ih,
    },
    {
      cases e1_ih with e1' e1_ih,
      use Term.Ap e1' e2,
      exact step.Ap1 e1 e1' e2 e1_ih,
    },
  },
  { exact or.inl value.Unit },
  { exact or.inl (value.Nat n) },
  {
    right,
    cases ih_h1,
    {
      cases ih_h2,
      {
        cases CFL_Nat h1 ih_h1 with n hn,
        cases CFL_Nat h2 ih_h2 with m hm,
        use Term.Nat (n+m),
        rw hn,
        rw hm,
        exact step.PlusNat n m,
      },
      {
        cases ih_h2 with e2' ih_e2,
        use Term.Plus e1 e2',
        exact step.Plus2 e1 e2' e2 ih_e2,
      },
    },
    {
      cases ih_h1 with e1' ih_e1,
      use Term.Plus e1' e2,
      exact step.Plus1 e1 e1' e2 ih_e1,
    }
  }
end

lemma inversion_Lam {Γ : Context} {x : var} {τ τ₁ : Typ} {t : Term} (h : has_type Γ (Term.Lam x τ₁ t) τ) : ∃ τ₂, τ = (τ₁ → τ₂) ∧ has_type (Dict.add Γ x τ₁) t τ₂
:=
begin 
  cases h with _ _ _ _ _ _ _ τ₂ _ h',
  use τ₂,
  exact ⟨rfl, h'⟩,
end

lemma inversion_Ap {Γ : Context} {e1 e2 : Term} {τ : Typ} (h : has_type Γ (Term.Ap e1 e2) τ) : ∃ τ₁ τ₂, τ = τ₂ ∧ has_type Γ e1 (τ₁ → τ₂) ∧ has_type Γ e2 τ₁
:=
begin 
  cases h with _ _ _ _ _ _ _ _ _ _ _ τ' _ _ _ h1 h2,
  --rcases h with _| _| @⟨a, τ', c, d, e, h1, h2⟩,
  use [τ', τ],
  exact ⟨rfl, ⟨h1, h2⟩⟩,
end

lemma inversion_Nat {Γ : Context} {n : ℕ} {τ : Typ} (h : has_type Γ (Term.Nat n) τ) : τ = Typ.Nat
:=
begin 
  cases h,
  refl,
end

lemma inversion_Plus {Γ : Context} {e1 e2 : Term} {τ : Typ} (h : has_type Γ (Term.Plus e1 e2) τ) : τ = Typ.Nat ∧ has_type Γ e1 Typ.Nat ∧ has_type Γ e2 Typ.Nat
:=
begin 
  cases h,
  exact ⟨rfl, h_ᾰ, h_ᾰ_1⟩,
end

lemma inversion_Unit {Γ : Context} {n : ℕ} {τ : Typ} (h : has_type Γ (Term.Unit) τ) : τ = Typ.Unit
:=
begin 
  cases h,
  refl,
end

lemma free_in_context {x : var} {e : Term} {τ : Typ} {Γ : Context} 
  (h : x ∈ e) (h1 : has_type Γ e τ) : Dict.inDict Γ x :=
begin 
  induction' h, 
  { 
    rw Dict.inDict,
    cases h1 with _ _ _ h,
    intro h',
    rw h' at h,
    cases h },
  {
    rcases (inversion_Lam h1) with ⟨τ2, typ_eq, h'⟩,
    specialize ih h',
    simp only [Dict.inDict, Dict.add, Dict.get, h, if_false, ne.def] at ih,
    exact ih,
  },
  {
    rcases inversion_Ap h1 with ⟨τ1, τ2, -, h', -⟩,
    exact ih h',
  },
  {
    rcases inversion_Ap h1 with ⟨τ1, τ2, -, -, h'⟩,
    exact ih h',
  },
  {
    have inv := inversion_Plus h1,
    exact ih inv.2.1,
  },
  {
    have inv := inversion_Plus h1,
    exact ih inv.2.2,
  },
end

-- the next 3 theorems were a 15-312 HW
lemma not_free_correct (x : var) (e : Term) : xor (free_in x e) (not_free_in x e) :=
begin 
  rw xor,
  induction e with _ y τ M _ e1 e2 e1_ih e2_ih _ e1 e2 e1_ih e2_ih,
  {
    by_cases x = e,
    {
      left,
      split,
        {
          rw ← h,
          exact free_in.Var x,
        },
        {
          intro h',
          cases h',
          contradiction,
        }
    },
    {
      right,
      split,
      {
        exact not_free_in.Var x e h,
      },
      {
        intro h',
        cases h',
        contradiction,
      },
    },
  },
  {
    cases e_ih,
    {
      by_cases this : x = y,
      {
        right,
        split,
        {
          rw this,
          exact not_free_in.Lam2 y τ M,
        },
        {
          intro h',
          cases h',
          contradiction,
        },
      },
      {
        left,
        split,
        {
          exact free_in.Lam x y τ M this e_ih.1,
        },
        {
          intro h',
          cases h',
          exact e_ih.2 h'_ᾰ_1,
          exact this rfl,
        },
      },
    },
    {
      by_cases this : x = y,
      {
        right,
        split,
        {
          rw this,
          exact not_free_in.Lam2 y τ M,
        },
        {
          intro h',
          cases h',
          contradiction,
        },
      },
      {
        right,
        split,
        {
          exact not_free_in.Lam1 x y τ M this e_ih.1,
        },
        {
          intro h',
          cases h',
          exact e_ih.2 h'_ᾰ_1,
        }
      },
    },
  },
  {
   cases e1_ih,
   cases e2_ih,
   repeat {
    left,
    split,
    {
      exact free_in.Ap1 x e1 e2 e1_ih.1,
    },
    {
      intro h',
      cases h',
      exact e1_ih.2 h'_ᾰ,
    },
   },
  cases e2_ih,
  {
    left,
    split,
    {
      exact free_in.Ap2 x e1 e2 e2_ih.1,
    },
    {
      intro h',
      cases h',
      exact e2_ih.2 h'_ᾰ_1,
    }
  },
  {
    right,
    split,
    {
      exact not_free_in.Ap x e1 e2 e1_ih.1 e2_ih.1,
    },
    {
      intro h',
      cases h',
      exact e1_ih.2 h'_ᾰ,
      exact e2_ih.2 h'_ᾰ,
    },
  },
  },
  {
    right,
    split,
    exact not_free_in.Nat x e,
    intro h',
    cases h',
  },
  {
    cases e1_ih,
    {
      cases e2_ih,
      {
        left,
        split,
        {
          exact free_in.Plus1 x e1 e2 e1_ih.1,
        },
        {
          intro h',
          cases h',
          exact e1_ih.2 h'_ᾰ,
        },
      },
      {
        left,
        split,
        {
          refine free_in.Plus1 x e1 e2 e1_ih.1,
        },
        {
          intro h',
          cases h',
          exact e1_ih.2 h'_ᾰ,
        },
      },
    },
    {
      cases e2_ih,
      {
        left,
        split,
        {
          refine free_in.Plus2 x e1 e2 e2_ih.1,
        },
        {
          intro h',
          cases h',
          exact e2_ih.2 h'_ᾰ_1,
        },
      },
      {
        right,
        split,
        {
          refine not_free_in.Plus x e1 e2 e1_ih.1 e2_ih.1,
        },
        {
          intro h',
          cases h',
          exact e1_ih.2 h'_ᾰ,
          exact e2_ih.2 h'_ᾰ,
        },
      },
    },
  },
  {
    right,
    split,
    exact not_free_in.Unit x,
    intro h',
    cases h',
  },
end

lemma not_free_correct' {x : var} {e : Term} : not_free_in x e ↔ ¬free_in x e :=
begin 
  have this := not_free_correct x e,
  rw xor at this,
  split,
  {
    intro h,
    intro h',
    cases this,
    {
      exact this.2 h,
    },
    {
      exact this.2 h',
    },
  },
  {
    intro h,
    cases this,
    {
      exfalso,
      exact h this.1,
    },
    {
      exact this.1,
    },
  },
end

-- you could do this in 1 line from not_free_correct'
-- but it requires double negation elim :pensive:

lemma free_correct {x : var} {e : Term} : free_in x e ↔ ¬ not_free_in x e :=
begin
  have this := not_free_correct x e,
  split,
  {
    intro h,
    cases this, 
    {
      exact this.2,
    },
    {
      exfalso,
      exact this.2 h,
    },
  },
  {
    intro h',
    cases this,
    {
      exact this.1,
    },
    {
      exfalso,
      exact h' this.1,
    },
  },
end 

lemma subCtxDerive {Γ Γ' : Context} {h : Dict.subDictOf Γ Γ'} {e : Term} {τ : Typ} 
  (h1 : has_type Γ e τ) : has_type Γ' e τ 
:=
begin 
  rw Dict.subDictOf at h,
  induction' e,
  {
    specialize h x,
    unfold has_mem.mem at h,
    by_cases this : Dict.inDict Γ x, 
    {
      specialize h this,
      cases h1,
      rw h1_ᾰ at h,
      exact has_type.Var Γ' x τ (eq.symm h),
    },
    {
      cases h1,
      rw Dict.inDict at this,
      specialize h (Dict.getSome h1_ᾰ),
      rw h at h1_ᾰ,
      exact has_type.Var Γ' x τ h1_ᾰ,
    },
  },
  {
    rcases inversion_Lam h1 with ⟨τ₁, ⟨τ_eq, h'⟩⟩,
    rename x_1 τ2,
    specialize @ih (Dict.add Γ x τ2) (Dict.add Γ' x τ2) τ₁,
    suffices : ∀ (k : var), (Dict.inDict (Dict.add Γ x τ2)) k → 
                            Dict.get (Dict.add Γ x τ2) k = Dict.get (Dict.add Γ' x  τ2) k, {
      simp only at this,
      specialize ih this,
      rw τ_eq,
      specialize ih h',
      exact has_type.Lam Γ' x τ2 τ₁ e ih,
    },
    intros k kh,
    specialize h k,
    simp only [Dict.get, Dict.add],
    split_ifs with lem,
    { refl },
    {
      unfold has_mem.mem at h,
      suffices : Dict.inDict Γ k, {
        specialize h this,
        repeat {rw Dict.get at h},
        exact h,
      },
      simp only [Dict.add, Dict.inDict, Dict.get, lem, if_false, ne.def] at kh,
      exact kh,
    },
  },
  {
    rcases inversion_Ap h1 with ⟨τ₁, τ₂, ⟨typ_eq, ⟨e1_typ, e2_typ⟩⟩⟩,
    specialize ih_e h e1_typ,
    specialize ih_e_1 h e2_typ,
    rw typ_eq,
    exact has_type.Ap Γ' τ₁ τ₂ e e_1 ih_e ih_e_1,
  },
  {
    cases h1,
    exact has_type.Nat Γ' n,
  },
  {
    cases inversion_Plus h1 with typ_eq inv,
    specialize ih_e h inv.1,
    specialize ih_e_1 h inv.2,
    rw typ_eq,
    exact has_type.Plus Γ' e e_1 ih_e ih_e_1,
  },
  {
    cases h1,
    exact has_type.Unit Γ',
  },
end

lemma contextWeakening {Γ Γ' : Context} {e : Term} {τ : Typ} 
  (h1 : Dict.subDictOf Γ Γ') (h2 : has_type Γ e τ) : has_type Γ' e τ
:=
begin 
  induction h2 with Γ _ _ h2i _ _ _ _ _ h2i _ _ _ _ _ _ h2 h2' h2'' h2_ih _ _ _ Γ e1 e2 h_e1 h_e2 e1_ih e2_ih,
  {
    refine has_type.Var Γ' h2_x h2_τ _,
    rw Dict.subDictOf at h1,
    specialize h1 h2_x (Dict.getSome h2i),
    rw ← h1,
    exact h2i,
  },
  {
    refine has_type.Lam Γ' h2_x h2_τ₁ h2_τ₂ h2_t₁ _,
    clear h2_ih,
    apply subCtxDerive,
    exact Dict.subDictAdd h1 h2_x h2_τ₁,
    exact h2i,
  },
  {
    specialize h2_ih h1,
    specialize h2'' h1,
    exact has_type.Ap Γ' h2_τ₁ h2_τ₂ h2_e₁ h2_e₂ h2'' h2_ih,
  },
  { exact has_type.Unit Γ', },
  { exact has_type.Nat Γ' h2_n, },
  {
    specialize e1_ih h1,
    specialize e2_ih h1,
    exact has_type.Plus Γ' e1 e2 e1_ih e2_ih,
  }
end

lemma emptyWeak {Γ : Context} {e : Term} {τ : Typ} (h : has_type ctx_Empty e τ) : has_type Γ e τ 
  := contextWeakening (Dict.emptySubdictAll Γ) h

lemma substPresTyp {Γ : Context} {x : var} {t v : Term} {τ τ₁: Typ} :
  has_type (Dict.add Γ x τ) t τ₁ -> has_type ctx_Empty v τ -> has_type Γ ([v // x]t) τ₁
:=
begin 
  intros h h_v,
  induction' t with y y τ' e,
  {
    rw subst,
    split_ifs with h',
    {
      rw h' at h,
      cases h with _ _ _ h,
      simp only [Dict.get, eq_self_iff_true, if_true] at h,
      rw ← (option.some.inj h),
      exact emptyWeak h_v,
    },
    {
      cases h with _ _ _ h,
      simp only [Dict.get, h', if_false] at h,
      exact has_type.Var Γ y τ₁ h,
    },
  },
  {
    rw subst,
    rcases (inversion_Lam h) with ⟨τ₂, typ_eq, h_inv⟩,
    split_ifs with h',
    {
      rw typ_eq,
      refine has_type.Lam Γ y τ' τ₂ e _,
      rw h' at h_inv,
      suffices : (Dict.add (Dict.add Γ y τ) y τ') = Dict.add Γ y τ', {
        rw ← this,
        exact h_inv,
      },
      simp only [Dict.add],
      funext,
      split_ifs,
      repeat {refl},
    },
    {
       suffices : (Dict.add (Dict.add Γ x τ) y τ') = (Dict.add (Dict.add Γ y τ') x τ), {
        rw this at h_inv,
        specialize ih h_v h_inv,
        rw typ_eq,
        exact has_type.Lam Γ y τ' τ₂ ([v//x]e) ih,
      },
      simp only [Dict.add],
      funext,
      split_ifs,
      {
        rw h_2 at h_1,
        exfalso,
        exact h' h_1,
      },
      repeat {refl},
    },
  },
  {
    rcases inversion_Ap h with ⟨τ₁, τ₂, ⟨inv_L, inv_M, inv_R⟩⟩,
    specialize ih_t h_v inv_M,
    specialize ih_t_1 h_v inv_R,
    rw inv_L,
    rw subst,
    exact has_type.Ap Γ τ₁ τ₂ ([v//x]t) ([v//x]t_1) ih_t ih_t_1,
  },
  {
    cases h,
    exact has_type.Nat Γ n,
  },
  {
    cases inversion_Plus h with typ_eq inv,
    rw subst,
    specialize ih_t h_v inv.1,
    specialize ih_t_1 h_v inv.2,
    rw typ_eq,
    exact has_type.Plus Γ ([v//x]t) ([v//x]t_1) ih_t ih_t_1,
  },
  {
    cases h,
    exact has_type.Unit Γ,
  },
end

theorem preservation {e e' : Term} {τ : Typ} 
(h1 : has_type ctx_Empty e τ) (h2 : e ↦ e') : has_type ctx_Empty e' τ :=
begin 
  induction' h2 with _ _ _ _ h' _ _ _ ih1 ih2,
  {
    cases h1 with _ _ _ _ _ _ _ _ _ _ _ τ1 _ _ _  h' h'',
    have inv := inversion_Lam h',
    rcases inv with ⟨τ₂, typ_eq, h_e⟩,
    rw ← (fn_typ_eq typ_eq).2 at h_e,
    rw (fn_typ_eq typ_eq).1 at h'',
    exact substPresTyp h_e h'',
  },
  {
    have inv := inversion_Ap h1,
    rcases inv with ⟨τ₁, τ₂, inv⟩,
    specialize ih2 inv.2.1,
    rw inv.1,
    exact has_type.Ap ⬝ τ₁ τ₂ e' e2 ih2 inv.2.2,
  },
  {
    have inv := inversion_Ap h1,
    rcases inv with ⟨τ₁, τ₂, inv⟩,
    specialize ih inv.2.2,
    rw inv.1,
    refine has_type.Ap ⬝ τ₁ τ₂ e1 e' inv.2.1 ih,
  },
  {
    cases inversion_Plus h1 with typ_eq inv,
    specialize ih inv.1,
    rw typ_eq,
    exact has_type.Plus ⬝ e' e2 ih inv.2,
  },
  {
    cases inversion_Plus h1 with typ_eq inv,
    specialize ih inv.2,
    rw typ_eq,
    exact has_type.Plus ⬝ e1 e' inv.1 ih,
  },
  {
    cases inversion_Plus h1 with typ_eq inv,
    rw typ_eq,
    exact has_type.Nat ⬝ (n + m),
  }
end