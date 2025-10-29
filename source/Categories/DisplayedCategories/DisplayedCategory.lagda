Anna Williams, 28 October 2025

Definition of a displayed category.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_∘_ ; id)
open import UF.Base
open import UF.Equiv
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

  cmp-right-id  : {a b : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} → (f : mor-fam f' x y) → transport (λ v → mor-fam v x y) (right-id {{C ₚ}} f') f ＝ comp f (id-fam x)

  cmp-left-id : {a b : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {x : obj-fam a} {y : obj-fam b} → (f : mor-fam f' x y) → transport (λ v → mor-fam v x y) (left-id {{C ₚ}} f') f ＝ comp (id-fam y) f
  
  cmp-assoc    : {a b c d : obj (C ₚ)} {f' : hom {{C ₚ}} a b} {g' : hom {{C ₚ}} b c} {h' : hom {{C ₚ}} c d} {x : obj-fam a} {y : obj-fam b} {z : obj-fam c} {w : obj-fam d} {f : mor-fam f' x y} {g : mor-fam g' y z} {h : mor-fam h' z w} → transport (λ v → mor-fam v x w) (assoc {{C ₚ}}) (comp h (comp g f)) ＝ comp (comp h g) f

\end{code}

We can now define a total category.

\begin{code}

{-
TotalCategory : {𝓦 𝓨 : Universe} {C : Category 𝓤 𝓥} (D : DisplayedCategory 𝓦 𝓨 C) → Category (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
TotalCategory {𝓤} {𝓥} {𝓦} {𝓨} {C} D = record { precategory = precategory ; id-equiv-iso = {!!} }
 where
  precategory : Precategory (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓨)
  precategory = record
                 { obj = Σ a ꞉ (obj (C ₚ)) , DisplayedCategory.obj-fam D a
                 ; hom = λ (a , x) (b , y) → Σ f ꞉ hom {{C ₚ}} a b , DisplayedCategory.mor-fam D f x y
                 ; hom-is-set = Σ-is-set (hom-is-set {{C ₚ}}) (λ _ → DisplayedCategory.mor-fam-is-set D)
                 ; id = λ (a , x) → (id {{C ₚ}}) , DisplayedCategory.id-fam D x
                 ; _∘_ = λ (f , f') (g , g') → _∘_ {{C ₚ}} f g , DisplayedCategory.comp D f' g'
                 ; left-id = λ (f , f') → to-Σ-＝ (left-id {{C ₚ}} f , DisplayedCategory.cmp-left-id D f')
                 ; right-id = λ (f , f') → to-Σ-＝ (right-id {{C ₚ}} f , DisplayedCategory.cmp-right-id D f')
                 ; assoc = to-Σ-＝ (assoc {{C ₚ}} , DisplayedCategory.cmp-assoc D)
                 }

  id-equiv-iso : (a b : obj precategory) → (a ＝ b) ≃ Cat-Iso {{precategory}} a b
  id-equiv-iso (a , x) (b , y) = id-iso , is-equivn
   where
    id-iso : a , x ＝ b , y → Cat-Iso {{precategory}} (a , x) (b , y)
    id-iso = id-to-iso {{precategory}} (a , x) (b , y)

    is-equivn : is-equiv id-iso
    is-equivn = (isomorphism , left-inv) , (isomorphism , right-inv)
     where
      isomorphism : Cat-Iso {{precategory}} (a , x) (b , y) → a , x ＝ b , y
      isomorphism ((f , f') , is-iso) = {!back-eqtofun (Category.id-equiv-iso C a b)!}

      left-inv : (λ x₁ → id-iso (isomorphism x₁)) ∼ (λ x₁ → x₁)
      left-inv v = {!!}

      right-inv : (λ x₁ → isomorphism (id-iso x₁)) ∼ (λ x₁ → x₁)
      right-inv v = {!!}
-}

\end{code}

We can now show that the obvious forgetful functor exists

\begin{code}

{-
forgetful : {𝓦 𝓨 : Universe} {C : Category 𝓤 𝓥} {D : DisplayedCategory 𝓦 𝓨 C} → Functor ((TotalCategory D)ₚ) (C ₚ)
forgetful {_} {_} {_} {_} {C} {D} = record { Fobj = pr₁ ; Fhom = pr₁ ; id-pres = id-pres ; distrib = distribute }
 where
  id-pres : (a : obj ((TotalCategory D)ₚ)) → pr₁ (Precategory.id (Category.precategory (TotalCategory D)) a) ＝ id {{C ₚ}}
  id-pres a = refl

  distribute : {a b c : obj (TotalCategory D ₚ)} {f : hom {{TotalCategory D ₚ}} a b}
      {g : Precategory.hom (TotalCategory D ₚ) b c} →
      pr₁ (_∘_ {{TotalCategory D ₚ}} g f) ＝ _∘_ {{C ₚ}} (pr₁ g) (pr₁ f)
  distribute = refl
-}

\end{code}
