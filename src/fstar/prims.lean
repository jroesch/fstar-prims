namespace fstar

def pure_pre := Prop
def pure_post (A : Type) := A -> Prop

-- For the VC generation
constant FStar.Tactics.Effect.Tac (A : Type) : Prop
def Prims.unit := unit
constant lean : unit -> FStar.Tactics.Effect.Tac unit

@[reducible] def pos := { x : nat // 0 < x }
@[reducible] def pos.mk (n : nat) (prf : 0 < n) : pos := subtype.mk n prf

instance pos_to_nat : has_coe pos nat :=
⟨ fun p, p.val ⟩

instance pos_has_le : has_le pos :=
⟨ fun a b, a.val <= b.val ⟩

instance pos_has_mul : has_mul pos :=
⟨ fun a b, ⟨ a.val * b.val,
    begin
        cases a, cases b,
        dsimp, admit
    end
 ⟩⟩

@[simp] lemma simp_pos_le :
    forall (a b : pos),
    (a <= b) = (a.val <= b.val) :=
begin
    intros, trivial
end

@[simp] lemma simp_pos_mul :
    forall (a b : nat) (aprf : 0 < a) (bprf : 0 < b),
    ((pos.mk a aprf) * (pos.mk b bprf)).val = a * b :=
begin
    intros, trivial
end

open tactic

meta def break_pos : tactic unit :=
do ls ← local_context,
   revert_lst ls,
   n ← mk_fresh_name,
   repeat $ do
     loc ← intro n,
     ty ← infer_type loc,
     if (ty = `(fstar.pos))
     then cases loc
     else return ()

end fstar

