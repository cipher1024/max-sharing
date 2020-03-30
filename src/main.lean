
import data.finmap
import data.quot
import tactic.basic
import tactic.linarith

universes u v

namespace tactic.interactive
setup_tactic_parser
open tactic

meta def check_types : tactic unit :=
-- meta def check_types (pat : parse texpr) : tactic unit :=
-- do es ← tactic.match_target pat,
--    trace es
do `(%%x = %%y) ← target,
   trace!"{x} : {infer_type x}",
   trace!"{y} : {infer_type y}"

-- example : 1 = 2 :=
-- begin
--   -- check_types _ = _,
--   -- check_types λ (t : Type u) (x y : t), x = y,
-- end

end tactic.interactive


namespace sigma

lemma fst_comp_map {α α'} {β : α → Sort*} {β' : α' → Sort*}
  (f : α → α') (g : ∀ x, β x → β' (f x)) :
  fst ∘ map f g = f ∘ fst :=
by ext ⟨a,b⟩; refl

end sigma

@[reducible]
def finmap' (α : Type u) (β : Type v) := finmap (λ _ : α, β)

namespace finmap

variables {α : Type u}
  {β : α → Type v}
variables
  [decidable_eq α]
  [∀ x, decidable_eq $ β x]
  {m : finmap β}

lemma insert_eq_self_of_lookup_eq {x : α} {y : β x}
  (h : m.lookup x = some y) : m.insert x y = m :=
begin
  ext1 k, by_cases h' : k = x; [subst h', skip];
  simp [lookup_insert,*],
end

lemma insert_lookup_of_eq {x x' : α} {y : β x}
  (h : x = x') : (m.insert x y).lookup x' = some (h.rec y) :=
by subst h; rw lookup_insert

protected def map {γ : α → Type*} (f : ∀ x, β x → γ x) (m : finmap β) : finmap γ :=
-- list.to_finmap $ list.map _ $ m.to_list
{ entries := m.entries.map $ sigma.map id f,
  nodupkeys :=
  begin
    induction h : m.entries using quot.induction_on,
    simp only [multiset.coe_map, multiset.coe_nodupkeys, multiset.quot_mk_to_coe''],
    rw [list.nodupkeys,list.keys,list.map_map,sigma.fst_comp_map,function.comp.left_id],
    have := m.nodupkeys, simp [h,list.nodupkeys,list.nodup] at this,
    exact this,
  end }

lemma lookup_insert_eq_ite  {x x' : α} {y : β x} :
  lookup x' (insert x y m) =
  if h : x' = x then some (h.symm.rec y) else lookup x' m :=
by split_ifs; [subst h, skip]; simp *

lemma lookup_insert_eq_ite' {β} (m : finmap' α β) {x x' : α} {y : β} :
  lookup x' (insert x y m) =
  if x' = x then some y else lookup x' m :=
by split_ifs; [subst h, skip]; simp *

lemma map_lookup_insert_eq_ite {γ} {x x' : α} {y : β x} (f : ∀ a, β a → γ) :
  f _ <$> lookup x' (insert x y m) =
  if h : x' = x then some (f _ y) else f _ <$> lookup x' m :=
by split_ifs; [subst h, skip]; simp *

variables {γ : Type u} {F : Type u → Type v}
  [functor F] [is_lawful_functor F]
open function functor

lemma map_injective_of_injective
  [nonempty α] (f : α → γ)
  (h : injective f) :
  injective (map f : F α → F γ) :=
begin
  intros x y h₀,
  have h₂ := congr_arg (map (inv_fun f)) h₀,
  simp only [map_map,inv_fun_comp h,map_id,id] at h₂,
  exact h₂
end

end finmap

@[derive decidable_eq]
inductive bdd
| var : ℕ → bdd
| nand : bdd → bdd → bdd

abbreviation ptr := unsigned
open bdd

@[derive decidable_eq]
inductive bdd_impl (s : Type) : Type
| var (v : ℕ) : s → bdd_impl
| nand : bdd_impl → bdd_impl → s → bdd_impl

variables {s : Type}

inductive bdd_impl.subtree (t : bdd_impl s) : bdd_impl s → Prop
| refl : bdd_impl.subtree t
| step_left (p) (t₀ : bdd_impl s)
            (t₁ : bdd_impl s) :
  bdd_impl.subtree t₀ →
  bdd_impl.subtree (bdd_impl.nand t₀ t₁ p)
| step_right (p) (t₀ : bdd_impl s)
             (t₁ : bdd_impl s) :
  bdd_impl.subtree t₁ →
  bdd_impl.subtree (bdd_impl.nand t₀ t₁ p)

namespace bdd_impl.subtree
open bdd_impl
lemma trans {t₀ t₁ : bdd_impl s} (ha : subtree t₀ t₁) : Π {t₂}, subtree t₁ t₂ → subtree t₀ t₂
| _ (subtree.refl t₁) := ha
| _ (subtree.step_left  p ta₂ tb₂ ha₂) := subtree.step_left p _ _ (trans ha₂)
| _ (subtree.step_right p ta₂ tb₂ hb₂) := subtree.step_right p _ _ (trans hb₂)

lemma sizeof_le_sizeof_of_subtree {t₀ : bdd_impl s} : Π {t₁}, subtree t₀ t₁ → sizeof t₀ ≤ sizeof t₁
| _ (subtree.refl _) := le_refl _
| _ (subtree.step_left p ta tb h) :=
  le_trans (sizeof_le_sizeof_of_subtree h)
    (le_of_lt $ by well_founded_tactics.default_dec_tac)
| _ (subtree.step_right p ta tb h) :=
  le_trans (sizeof_le_sizeof_of_subtree h)
    (le_of_lt $ by well_founded_tactics.default_dec_tac)

lemma antisymm {t₀ t₁ : bdd_impl s} (ha : subtree t₀ t₁) (hb : subtree t₁ t₀) : t₀ = t₁ :=
begin
  induction ha generalizing hb,
  { refl },
  all_goals
  { specialize ha_ih (trans (subtree.step_left _ _ _ $ subtree.refl _) hb) <|>
      specialize ha_ih (trans (subtree.step_right _ _ _ $ subtree.refl _) hb),
    cases hb; clear hb,
    { refl },
    all_goals
    { replace ha_a := sizeof_le_sizeof_of_subtree ha_a,
      replace hb_a := sizeof_le_sizeof_of_subtree hb_a,
      simp [sizeof,has_sizeof.sizeof,bdd_impl.sizeof] at ha_a hb_a,
      have : 1 + bdd_impl.sizeof _ ha_t₀ ≤ bdd_impl.sizeof _ ha_t₀,
      { linarith },
      apply absurd this, simp } },
end

lemma subtree_of_subtree_of_to_spec_eq_to_spec {p₀ p₁} {ta tb : bdd_impl s}
  (h₂ : subtree (bdd_impl.nand ta tb p₀) (bdd_impl.nand ta tb p₁)) :
  p₀ = p₁ :=
begin
  generalize_hyp h : bdd_impl.nand p₀ ta tb = t at h₂,
  generalize_hyp h' : bdd_impl.nand p₁ ta tb = t' at h₂,
  induction t' generalizing p₀ ta tb t,
  { cases h', },
  cases h₂,
  { injection h', injection h, subst_vars },
  {
    specialize t'_ih_a _ _ h', },
  {  },
  induction h₂,
  { subst h', injection h, },
  { apply h₂_ih, },
  suffices : t = bdd_impl.nand p₁ ta tb,
  { subst t, injection this },
  let p := p₁,
  induction h₂,
  { refl },
  -- all_goals
  { specialize h₂_ih (trans (subtree.step_left _ _ _ $ subtree.refl _) _),
      -- specialize ha_ih (trans (subtree.step_right _ _ _ $ subtree.refl _) hb),
    cases hb; clear hb,
    { refl },
    all_goals
    { replace ha_a := sizeof_le_sizeof_of_subtree ha_a,
      replace hb_a := sizeof_le_sizeof_of_subtree hb_a,
      simp [sizeof,has_sizeof.sizeof,bdd_impl.sizeof] at ha_a hb_a,
      have : 1 + bdd_impl.sizeof ha_t₀ ≤ bdd_impl.sizeof ha_t₀,
      { linarith },
      apply absurd this, simp } },
 --  -- have h := h₂,
 --  suffices : subtree (bdd_impl.nand p₁ ta tb) (bdd_impl.nand p₀ ta' tb'),
 --  { subst_vars, have := bdd_impl.subtree.antisymm h₂ this,
 --    injection this },
 --  cases h₂,
 --  { exact h₂ },
 --  { subst ta', induction ta,
 --    { cases h₂_a },
 --    {
 --      -- generalize_hyp : (bdd_impl.nand p₀ (bdd_impl.nand ta_p ta_a ta_a_1) tb) at h₂_a,
 --      -- cases h₂_a,
 --      have := subtree.step_left _ _ _ h₂_a,
 --  } },
 --  -- clear h,
 --  { induction ta' generalizing ta tb p₀, cases h₂_a,

 --    -- generalize_hyp ha : bdd_impl.nand p₀ (bdd_impl.nand ta_p ta_a ta_a_1) tb = t at h₀_a,
 --    cases h₂_a,
 --    { exact ta'_ih_a rfl h₂ (bdd_impl.subtree.subtree_of_eq h₀.symm) },
 --    { subst ta, specialize ta'_ih_a _ h₂ h₂_a_a, },
 --    rw ← h₀ at h₂_a,

 -- },
 --  -- induction h₀,
end

lemma subtree_of_eq {t₀ t₁ : bdd_impl s} (h : t₀ = t₁) : t₀.subtree t₁ :=
h ▸ subtree.refl _
-- lemma ext {t₀ t₁ : bdd_impl} (h : ∀ x, subtree x t₀ ↔ subtree x t₁) : t₀ = t₁

end bdd_impl.subtree

def bdd_impl.ssubtree (t t' : bdd_impl s) : Prop :=
t.subtree t' ∧ t ≠ t'

namespace bdd_impl.ssubtree
open bdd_impl
lemma trans {t₀ t₁ t₂ : bdd_impl s} (ha : ssubtree t₀ t₁) (hb : ssubtree t₁ t₂) : ssubtree t₀ t₂ :=
have hc : subtree t₀ t₂, from ha.1.trans hb.1,
⟨ hc, λ h₁,
  have hc' : subtree t₂ t₀, from h₁ ▸ subtree.refl _,
  have ha' : subtree t₁ t₀, from hb.1.trans hc',
  ha.2 $ ha.1.antisymm ha' ⟩

lemma irrefl (t₀ : bdd_impl s) : ¬ ssubtree t₀ t₀ :=
λ h, h.2 rfl

lemma antisymm {t₀ t₁ : bdd_impl s} (ha : ssubtree t₀ t₁) (hb : ssubtree t₁ t₀) : false :=
ha.2 $ ha.1.antisymm hb.1

end bdd_impl.ssubtree


def trivial_impl : Π (d : bdd), bdd_impl ℕ
| (var v) := bdd_impl.var v 0
| (nand l r) := bdd_impl.nand (trivial_impl l) (trivial_impl r) 0

@[simp]
def ptr_addr : bdd_impl s → s
| (bdd_impl.var _ p) := p
| (bdd_impl.nand _ _ p) := p

@[simp]
def bdd_impl.to_spec : bdd_impl s → bdd
| (bdd_impl.var v _) := var v
| (bdd_impl.nand l r _) := nand (bdd_impl.to_spec l) (bdd_impl.to_spec r)

@[simp]
def bdd_impl.to_spec_trivial_impl (d : bdd) : (trivial_impl d).to_spec = d :=
begin
  induction d; simp [trivial_impl,bdd_impl.to_spec,*],
end

-- @[simp]
-- def bdd_impl.trivial_impl_to_spec (d : bdd_impl) : trivial_impl d.to_spec = d :=
-- begin
--   induction d; simp [trivial_impl,bdd_impl.to_spec,*],
-- end

-- #exit
def with_repr {α} (d : bdd) (f : Π {s} (d' : bdd_impl s), d'.to_spec = d → α)
  (h : ∀ s s' t t' h h', @f s t h = @f s' t' h') : α := f (trivial_impl d) (bdd_impl.to_spec_trivial_impl d)

structure bdd.package (p : Π {s}, bdd_impl s → Prop) :=
(val : bdd)
(repr : trunc (Σ' {s} (t : bdd_impl s), t.to_spec = val ∧ p t))
-- ← this `trunc` could have a special implementation

def bdd_impl' (s) (d : bdd) := { t : bdd_impl s // t.to_spec = d }

def max_sharing (t : bdd_impl s) : Prop :=
∀ {d} {t' : bdd_impl' s d} {t'' : bdd_impl' s d},
  t'.1.subtree t →
  t''.1.subtree t →
  t' = t''

structure nondup (s : Type) :=
(table : finmap' bdd (bdd_impl s))
(shared : ∀ (t : bdd_impl s) (t' : bdd_impl s),
  table.lookup t.to_spec = some t →
  t'.subtree t →
  table.lookup t'.to_spec = some t')
(consistent : ∀ {d t}, table.lookup d = some t → t.to_spec = d)

def intl_bdd (d : bdd) (tbl : nondup s) := { t : bdd_impl s // tbl.table.lookup d = some t }

namespace nondup

lemma intl_bdd_of_subtree {d : bdd} {tbl : nondup s} (it : intl_bdd d tbl) (t : bdd_impl s)
  (h : t.subtree it.val) : tbl.table.lookup t.to_spec = some t :=
begin
  apply tbl.shared _ _ _ h,
  convert it.2, apply tbl.consistent it.2,
end

variables (tbl : nondup s)

def mem (d : bdd) (tbl : nondup s) := d ∈ tbl.table

instance : has_mem bdd (nondup s) := ⟨ mem ⟩

def lookup (d : bdd) : option (intl_bdd d tbl) :=
match finmap.lookup d tbl.table, rfl : Π x, finmap.lookup d tbl.table = x → _ with
| none, h := none
| (some val), h := some ⟨val, h⟩
end

set_option pp.proofs true

lemma lookup_iff_map {d : bdd} (x : option (intl_bdd d tbl)) : lookup tbl d = x ↔ tbl.table.lookup d = subtype.val <$> x :=
begin
  rw [lookup],
  generalize : lookup._proof_1 tbl d = h, revert h,
  suffices : ∀ (y) (h : finmap.lookup d tbl.table = y),
    lookup._match_1 tbl d y h = x ↔ y = subtype.val <$> x,
    from this _,
  intros, cases y; rw lookup._match_1; cases x; simp,
  split; intros h; subst h; cases x, refl,
end

def bdd_impl'.var (v : ℕ) (p : s) : bdd_impl' s (var v) :=
⟨ bdd_impl.var v p, rfl ⟩

def bdd_impl'.nand {d d'} (t : bdd_impl' s d) (t' : bdd_impl' s d') (p : s) : bdd_impl' s (nand d d') :=
⟨ bdd_impl.nand t.val t'.val p, by simp [t.2,t'.2] ⟩

-- #check subtype.mk.inj_eq

lemma subtree_of_subtree_of_to_spec_eq_to_spec {p₀ p₁} {ta tb ta' tb' : bdd_impl s}
  (h₀ : ta = ta')
  (h₁ : tb = tb')
  (h₂ : subtree (bdd_impl.nand ta tb p₀) (bdd_impl.nand ta' tb' p₁)) :
  p₀ = p₁ :=
begin
  -- have h := h₂,
  suffices : subtree (bdd_impl.nand ta tb p₁) (bdd_impl.nand ta' tb' p₀),
  { subst_vars, have := bdd_impl.subtree.antisymm h₂ this,
    injection this },
  cases h₂,
  { exact h₂ },
  { subst ta', induction ta,
    { cases h₂_a },
    {
      -- generalize_hyp : (bdd_impl.nand p₀ (bdd_impl.nand ta_p ta_a ta_a_1) tb) at h₂_a,
      -- cases h₂_a,
      have := subtree.step_left _ _ _ h₂_a,
  } },
  -- clear h,
  { induction ta' generalizing ta tb p₀, cases h₂_a,

    -- generalize_hyp ha : bdd_impl.nand p₀ (bdd_impl.nand ta_p ta_a ta_a_1) tb = t at h₀_a,
    cases h₂_a,
    { exact ta'_ih_a rfl h₂ (bdd_impl.subtree.subtree_of_eq h₀.symm) },
    { subst ta, specialize ta'_ih_a _ h₂ h₂_a_a, },
    rw ← h₀ at h₂_a,

 },
  -- induction h₀,
end

lemma subtree_of_subtree_of_to_spec_eq_to_spec' {t₀ t₁ : bdd_impl s}
  (h₀ : subtree t₀ t₁)
  (h₁ : t₀.to_spec = t₁.to_spec) :
  t₀ = t₁ :=
begin
  induction t₁ generalizing t₀,
  { cases h₀, refl },
  { cases t₀, cases h₁,
    rw [bdd_impl.to_spec,bdd_impl.to_spec] at h₁,
    injection h₁, specialize t₁_ih_a _ h_1,
    specialize t₁_ih_a_1 _ h_2,
 }
end

-- lemma boo (t t' : bdd_impl s)
--     finmap.lookup (bdd_impl.to_spec t) (finmap.insert (bdd_impl.to_spec d) d tbl.table) = some t →
--     subtree t' t → finmap.lookup (bdd_impl.to_spec t') (finmap.insert (bdd_impl.to_spec d) d tbl.table) = some t'

lemma lookup_insert {s : Type}
  (tbl : nondup s)
  (d : bdd_impl s)
  (hd : ∀ (d' : bdd_impl s),
          subtree d' d →
          (d' ≠ d ↔
             finmap.lookup (bdd_impl.to_spec d') tbl.table = some d'))
  (t t' : bdd_impl s)
  (h₀ : finmap.lookup (bdd_impl.to_spec t)
            (tbl.table.insert (bdd_impl.to_spec d) d ) =
          some t)
  (h₁ : subtree t' t) :
  finmap.lookup (bdd_impl.to_spec t')
      (tbl.table.insert (bdd_impl.to_spec d) d) =
    some t' :=
begin
  classical,
  by_cases bdd_impl.to_spec d = bdd_impl.to_spec t,
  { rw [h,finmap.lookup_insert] at h₀,
    injection h₀, subst d, clear h h₀,
    have hd' := hd _ h₁,
    by_cases t' = t,
    { rw [h,finmap.lookup_insert] },
    { have h' := hd'.mp h,
      rwa [finmap.lookup_insert_eq_ite',if_neg],
      intro hh,
      -- specialize hd _ (subtree.refl _),
      replace hd := mt (hd t (subtree.refl _)).mpr (not_not_intro rfl),
      rw [← hh,h'] at hd,
      apply h,
      admit } },
  { have hd' := mt (hd d (subtree.refl _)).mpr (not_not_intro rfl),
    rw finmap.lookup_insert_of_ne at ⊢ h₀,
    apply tbl.shared _ _ h₀ h₁,
    { intro h, admit },
    { intro h, rw ← h at hd', }, }
end

lemma insert_consistent {s : Type} {d_1 : bdd}
  (tbl : nondup s)
  (d : bdd_impl s)
  (hd : ∀ (d' : bdd_impl s),
          subtree d' d →
          (d' ≠ d ↔
             finmap.lookup (bdd_impl.to_spec d') tbl.table = some d'))
  {t : bdd_impl s}
  (h₀ : finmap.lookup d_1 (tbl.table.insert (bdd_impl.to_spec d) d) = some t) :
  bdd_impl.to_spec t = d_1 :=
begin
  rw finmap.lookup_insert_eq_ite' at h₀, split_ifs at h₀,
  { cc },
  { exact tbl.consistent h₀, }
end

def insert (d : bdd_impl s) (p : s)
  -- (h : d.to_spec ∉ s.table )
  (hd : ∀ d', bdd_impl.subtree d' d → (d' ≠ d ↔ tbl.table.lookup d'.to_spec = some d')) : nondup s :=
⟨ tbl.table.insert d.to_spec d,
lookup_insert _ _ hd, λ _ _, insert_consistent tbl d hd ⟩

-- def insert_nand (d : bdd_impl s) (p : s)
--   -- (h : d.to_spec ∉ s.table )
--   (hd : ∀ d', bdd_impl.subtree d' d → (d' ≠ d ↔ tbl.table.lookup d'.to_spec = some d')) : nondup s :=


-- def insert' {v : ℕ} (p : s)
--   (h : var v ∉ tbl.table ) : nondup s :=
-- ⟨ tbl.table.insert (var v) (bdd_impl.var v p), _, _ ⟩

def insert_var {v : ℕ} (p : s)
  (h : var v ∉ tbl) : nondup s :=
⟨ tbl.table.insert (var v) (bdd_impl.var v p),
  begin
    introv ht hh,
    replace h : ∀ tt, ¬ tbl.table.lookup (var v) = some tt,
    { introv ht', apply h, change _ ∈ tbl.table,
      rw [finmap.mem_iff], exact ⟨_,ht'⟩ },
    rw finmap.lookup_insert_eq_ite', split_ifs with h₀,
    -- rw finmap.lookup_insert_eq_ite' at ht, split_ifs at ht,
    classical,
    by_cases h₁ : t = t',
    { rw [h₁,h₀,finmap.lookup_insert] at ht,
      injection ht, },
    { rw finmap.lookup_insert_eq_ite' at ht, split_ifs at ht,
      { admit },
      -- have h' := h (bdd_impl.var v p),
      { specialize h t', rw ← h₀ at h,
        have hh' := tbl.shared _ _ ht hh,
        exact absurd hh' h },
      { intro h₂, rw [h₂,finmap.lookup_insert] at ht, }},
    -- { rw finmap.lookup_insert_of_ne at ht,
    --   -- have h' := h (bdd_impl.var v p),
    --   { specialize h t', rw ← h₀ at h,
    --     have hh' := tbl.shared _ _ ht hh,
    --     exact absurd hh' h },
    --   { intro h₂, rw [h₂,finmap.lookup_insert] at ht, }},
  end, sorry ⟩

def insert_nand {d d' : bdd} (t : intl_bdd d tbl) (t' : intl_bdd d' tbl) (p : s)
  (h : nand d d' ∉ tbl) : nondup s :=
⟨ tbl.table.insert (nand d d') (bdd_impl.nand t.1 t'.1 p), _, _ ⟩

-- def insert {d d' : bdd} (t : intl_bdd d tbl) (t' : intl_bdd d' tbl) (p : ptr)
--   (h : nand d d' ∉ tbl.table ) : nondup s :=
-- ⟨ tbl.table.insert (nand d d') (bdd_impl.nand t.1 t'.1 p),
-- begin
--   intros d₀ t₀ d₁ t₁ h₀ h₁,
--   rw finmap.lookup_insert_eq_ite at h₀, split_ifs at h₀ with h',
--   { subst h', dsimp [] at h₀,
--     cases h₀, cases t₁, dsimp at h₁,
--     cases h₁,
--     { have : d₁ = (nand d d'),
--       { rw [← t₁_property,bdd_impl.to_spec,t.val.property,t'.val.property], },
--       subst this, rw [finmap.lookup_insert], refl },
--     { have : d₁ ≠ (nand d d'),
--       { intro h', subst h', apply h, -- rw ← t₁_property,
--         rw finmap.mem_iff, split,
--         apply s.inv t.val ⟨t₁_val,t₁_property⟩ t.property h₁_a, },
--       rw [finmap.lookup_insert_of_ne _ this],
--       apply s.inv t.val ⟨t₁_val,t₁_property⟩ t.property h₁_a },
--     { have : d₁ ≠ (nand d d'),
--       { intro h', subst h', apply h, -- rw ← t₁_property,
--         rw finmap.mem_iff, split,
--         apply s.inv t'.val ⟨t₁_val,t₁_property⟩ t'.property h₁_a, },
--       rw [finmap.lookup_insert_of_ne _ this],
--       apply s.inv t'.val ⟨t₁_val,t₁_property⟩ t'.property h₁_a } },
--   { have := s.inv t₀ t₁ h₀ h₁,
--     rwa finmap.lookup_insert_of_ne,
--     intro h₂, apply h, rw ← h₂, simp [finmap.mem_iff],
--     exact ⟨_,this⟩ }
-- end ⟩

-- def insert_nand_others {d d'} (t : bdd_impl' d) (p : s) (h) (d₂)
--   (x : intl_bdd d₂ tbl) : intl_bdd d₂ (tbl.insert t p h) :=
-- ⟨ x.1, begin
--          dsimp [insert]; rw [finmap.lookup_insert_of_ne],
--          { apply x.property },
--          { intro h', rw ← h' at h, apply h,
--            rw finmap.mem_iff, exact ⟨_,x.2⟩ }
--        end  ⟩

def intl_var {d d'} (t : intl_bdd d s) (t' : intl_bdd d' s) (p : ptr) (h) :
  intl_bdd (nand d d') (s.insert t t' p h) :=

def intl_nand {d d'} (t : intl_bdd d s) (t' : intl_bdd d' s) (p : ptr) (h) :
  intl_bdd (nand d d') (s.insert t t' p h) :=
⟨ bdd_impl'.nand t.1 t'.1 p, by rw [insert,finmap.lookup_insert] ⟩

def M (s d) :=
Σ' (s' : nondup) (x : intl_bdd d s'), ∀ d', intl_bdd d' s → intl_bdd d' s'

def id' {s} : ∀ d', intl_bdd d' s → intl_bdd d' s := λ _, id

def M.pure {d} (x : intl_bdd d s) : M s d :=
⟨s, x, id'⟩

section
variable {s}

def M.bind {d d'} (x : M s d) (f : ∀ s', intl_bdd d s' → (∀ d, intl_bdd d s → intl_bdd d s') → M s' d') : M s d' :=
match x with
| ⟨s',b,g⟩ :=
  match f s' b g with
  | ⟨s'',c,h⟩ := ⟨s'',c,λ _, h _ ∘ g _⟩
  end
end
-- #exit
theorem M.pure_bind {d} (x : intl_bdd d s)
  (f : ∀ s', intl_bdd d s' → (∀ d, intl_bdd d s → intl_bdd d s') → M s' d) :
  M.bind (M.pure s x) f = f _ x (λ _, id) :=
begin
  rw [M.pure,M.bind,M.bind._match_1],
  rcases f s x id' with ⟨a,b,c⟩, refl
end

theorem M.bind_pure {d} (x : M s d) :
  M.bind x (λ s' a f, M.pure _ a) = x :=
begin
  rcases x with ⟨a,b,c⟩, refl,
end

theorem M.bind_bind {d d' d''} (x : M s d)
  (f : ∀ s', intl_bdd d s' → (∀ d, intl_bdd d s → intl_bdd d s') → M s' d')
  (g : ∀ s', intl_bdd d' s' → (∀ d, intl_bdd d s → intl_bdd d s') → M s' d'') :
  M.bind (M.bind x f) g = M.bind x (λ s' a h, M.bind (f s' a h) (λ s'' b h', g _ b (λ _, h' _ ∘ h _))) :=
begin
  rcases x with ⟨a,b,c⟩,
  simp [M.bind,M.bind._match_1],
  rcases (f a b c) with ⟨a₁,b₁,c₁⟩,
  simp [M.bind,M.bind._match_1],
  rcases (g a₁ b₁ (λ _, c₁ _ ∘ c _)) with ⟨a₂,b₂,c₂⟩,
  refl
end

end

def mk_var (p : ptr) (v : ℕ) : M s (var v) :=
match lookup s (var v), rfl : ∀ x, lookup s (var v) = x → _ with
| none, h := _
| (some val), h := ⟨s,val,λ _, id⟩
end

def mk_nand (p : ptr) : Π {d}, intl_bdd d s → Π {d'}, intl_bdd d' s → M s (nand d d')
| d t d' t' :=
  match lookup s (nand d d'), rfl : ∀ x, lookup s (nand d d') = x → _ with
  | none, h :=
    have nand d d' ∉ s.table, by { simp [lookup_iff_map] at h, simp [finmap.mem_iff,h], },
    ⟨_, insert_nand s t t' p this, insert_nand_others _ _ _ _ _⟩
  | (some val), h := ⟨_,val,λ _, id⟩
  end

def mk_nand' (p : ptr) {d d'} (t : intl_bdd d s) (t' : intl_bdd d' s) : M s (nand d d') :=
mk_nand s p t t'

end nondup
open nondup

def share_common : Π (d : bdd_impl) (s : nondup), M s d.to_spec
| (bdd_impl.var p v) s := ⟨_, _⟩
| (bdd_impl.nand p l r) s :=
M.bind (share_common l s) $ λ s' l' f₀,
M.bind (share_common r s') $ λ s'' r' f₁,
nondup.mk_nand' s'' p (f₁ _ l') r'
