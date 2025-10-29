Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import UF.Sets
open import UF.Sets-Properties

open import Categories.Category
open import Categories.Functor

module Categories.DisplayedCategories.DisplayedCategory where

\end{code}

We first define the notion of a displayed category. This is
exactly a category D and a functor F : D → C. Which satisfies
the usual structure of a category.

\begin{code}

record DisplayedCategory (𝓦 𝓨 : Universe) (C : Category 𝓤 𝓥) : ((𝓦 ⊔ 𝓨) ⊔ (𝓤 ⊔ 𝓥))⁺ ̇  where
 field
  obj-fam : (c : obj (C ₚ)) → 𝓦 ̇
  mor-fam : {a b : obj (C ₚ)} → (f : hom {{C ₚ}} a b) → (x : obj-fam a) → (y : obj-fam b)  → 𝓨 ̇
  mor-fam-is-set : {a b : obj (C ₚ)} {f : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} → is-set (mor-fam f x y)
  
  id-fam  : {c : obj (C ₚ)} → (x : obj-fam c) → mor-fam (id {{C ₚ}} {c}) x x

  comp    : {a b c : obj (C ₚ)} {g : hom {{C ₚ}} b c} {f : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} {z : obj-fam c}
          → (gyz : mor-fam g y z) → (fxy : mor-fam f x y) → mor-fam (_∘_ {{C ₚ}} g f) x z

  cmp-right-id  : {a b : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} → (f : mor-fam f' x y) → {!comp f (id-fam x) ? f!}

  cmp-left-id : {a b : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} → (f : mor-fam f' x y) → transport (λ v → mor-fam v x y) ((left-id {{C ₚ}} f')⁻¹) (comp (id-fam y) f) ＝ f
  
  cmp-assoc    : {a b c d : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {g' : hom {{C ₚ}} b c} {h' : hom {{C ₚ}} c d} {x : obj-fam a} {y : obj-fam b} {z : obj-fam c} {w : obj-fam d} {f : mor-fam f' x y} {g : mor-fam g' y z} {h : mor-fam h' z w} → transport (λ v → mor-fam v x w) (assoc {{C ₚ}}) (comp h (comp g f)) ＝ comp (comp h g) f

\end{code}

We can now define a total category.

\begin{code}

TotalCategory : {𝓦 𝓨 : Universe} {C : Category 𝓤 𝓥} (D : DisplayedCategory 𝓦 𝓨 C) → Category {!!} {!!}
TotalCategory {𝓤} {𝓥} {_} {_} {C} D = record { precategory = precategory ; id-equiv-iso = id-equiv-iso }
 where
  precategory : Precategory {!!} {!!}
  precategory = record
                 { obj = Σ a ꞉ (obj (C ₚ)) , DisplayedCategory.obj-fam D a
                 ; hom = λ (a , x) (b , y) → Σ f ꞉ hom {{C ₚ}} a b , DisplayedCategory.mor-fam D f x y
                 ; hom-is-set = Σ-is-set (hom-is-set {{C ₚ}}) (λ _ → DisplayedCategory.mor-fam-is-set D)
                 ; id = λ (a , x) → (id {{C ₚ}}) , DisplayedCategory.id-fam D x
                 ; _∘_ = λ (f , f') (g , g') → _∘_ {{C ₚ}} f g , DisplayedCategory.comp D f' g'
                 ; left-id = {!!}
                 ; right-id = {!!}
                 ; assoc = {!!}
                 }

  id-equiv-iso : {!!}
  id-equiv-iso a b = {!!} , ({!!} , {!!})

\end{code}
