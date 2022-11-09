import tactic 
structure Dict (α : Type*) (β : Type*) :=
  (data : α -> option β)

namespace Dict
  variables {α β : Type*}
  [decidable_eq α]

  def empty : Dict α β :=
    ⟨λ k, none⟩

  def add (d : Dict α β) (k : α) (e : β) : Dict α β :=
    ⟨λ k', if k' = k then e else d.data k'⟩
  
  def rem (d : Dict α β) (k : α) : Dict α β :=
    ⟨λ k', if k' = k then none else d.data k'⟩

  def get (d : Dict α β) (k : α) : option β := d.data k
  
  def inDict (d : Dict α β) (x : α) := d.get x ≠ none 

  instance : has_mem α (Dict α β) := ⟨λ k d, inDict d k⟩ 

  def subDictOf (d1 d2 : Dict α β) := ∀ k ∈ d1, d1.get k = d2.get k
  
  theorem emptySubdictAll (d : Dict α β) : subDictOf empty d := 
  begin 
    intros k h,
    exact congr_fun (false.rec (empty.get = λ (k : α), get d k) (h rfl)) k,
  end

  theorem subDictSelf (d : Dict α β) : subDictOf d d :=
  begin 
    intros k h,
    refl,
  end

  theorem getSome {d : Dict α β} {x : α} {y : β} : Dict.get d x = (some y) -> x ∈ d :=
  begin
    intro h,
    unfold has_mem.mem,
    rw inDict,
    rw h,
    simp only [ne.def, not_false_iff],
  end


  theorem subDictAdd {d1 d2 : Dict α β} (h : subDictOf d1 d2) : 
  ∀ k e, subDictOf (add d1 k e) (add d2 k e)
  :=
  begin
    intros k e k' h',
    simp only [add, get],
    split_ifs with lem,
    { refl },
    specialize h k',
    simp only [has_mem.mem, inDict, get, add, lem, if_false, ne.def] at h',
    exact h h',
  end
end Dict