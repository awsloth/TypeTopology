Anna Williams, 13 November 2025

The Category of Magmas

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Type hiding (id ; _∘_)
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_ ; _≅⟨_⟩_)
open import UF.FunExt
open import UF.Sets
open import UF.Sets-Properties
open import UF.SIP
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.Examples.Magma where

module _ {𝓤 : Universe} (fe : Fun-Ext) where
 Magma : (𝓤 ⁺) ̇
 Magma = Σ X ꞉ 𝓤 ̇ , (X → X → X) × is-set X

 MagmaWildcat : WildCategory (𝓤 ⁺) 𝓤
 MagmaWildcat = wildcat-make Magma
                             magma-hom
                             (λ {a} → magma-id {a})
                             (λ {a} {b} {c} → magma-comp {a} {b} {c})
                             (λ {a} {b} → magma-l-id {a} {b})
                             (λ {a} {b} → magma-r-id {a} {b})
                             λ {a} {b} {c} {d} {f} {g} {h} → magma-assoc {a} {b} {c} {d} {f} {g} {h}
  where
   magma-hom : (a b : Magma) → 𝓤 ̇
   magma-hom (X , _·_ , _) (Y , _*_ , _) = Σ f ꞉ (X → Y) , Π x ꞉ X , Π y ꞉ X , f (x · y) ＝ (f x) * (f y)

   magma-id : {a : Magma} → magma-hom a a
   magma-id = id , λ x y → refl

   magma-comp : {a b c : Magma} → magma-hom b c → magma-hom a b → magma-hom a c
   magma-comp {X , _·_ , _}
              {Y , _*_ , _}
              {Z , _∙_ , _}
              (f , fp)
              (g , gp) = (λ x → f (g x))
                       , λ x y → f (g (x · y))         ＝⟨ ap f (gp x y) ⟩
                                 f ((g x) * (g y))     ＝⟨ fp (g x) (g y) ⟩
                                 (f (g x)) ∙ (f (g y)) ∎

   magma-l-id : {a b : Magma} (f : magma-hom a b) → magma-comp {a} {b} {b} (magma-id {b}) f ＝ f
   magma-l-id {_} {_ , _ , sY} (f , pf) = to-Σ-＝ (refl , inverse _ (fe _ _) λ x → (inverse _ (fe _ _) λ y → sY _ (pf x y)))

   magma-r-id : {a b : Magma} (f : magma-hom a b) → magma-comp {a} {a} {b} f (magma-id {a}) ＝ f
   magma-r-id {_} {_ , _ , sY} (f , pf) = to-Σ-＝ (refl , inverse _ (fe _ _) λ x → (inverse _ (fe _ _) λ y → sY _ (pf x y)))

   magma-assoc : {a b c d : Magma}
                 {f : magma-hom a b}
                 {g : magma-hom b c}
                 {h : magma-hom c d}
               → magma-comp {a} {c} {d} h (magma-comp {a} {b} {c} g f)
               ＝ magma-comp {a} {b} {d} (magma-comp {b} {c} {d} h g) f
   magma-assoc {_} {_} {_} {_ , _ , S} {f , pf} {g , pg} {h , ph} = to-Σ-＝ (refl , inverse _ (fe _ _) λ x → (inverse _ (fe _ _) λ y → S _ _))

\end{code}

We now show that this is a precategory

\begin{code}

 MagmaPrecategory : Precategory (𝓤 ⁺) 𝓤
 MagmaPrecategory = MagmaWildcat , is-pre
  where
   is-pre : is-precategory MagmaWildcat
   is-pre (X , _·_ , sX) (Y , _*_ , sY) = Σ-is-set (Π-is-set fe (λ x → sY)) (λ f → Π-is-set fe λ x → Π-is-set fe λ y → props-are-sets sY)

\end{code}

Now we look at SIP for ∞-Magmas and then add the axiom for magmas

\begin{code}

 open sip

 ∞-magma-structure : 𝓤 ̇ → 𝓤 ̇ 
 ∞-magma-structure X = X → X → X

 ∞-magma : 𝓤 ⁺ ̇
 ∞-magma = Σ X ꞉ 𝓤 ̇ , ∞-magma-structure X

 sns-data : SNS ∞-magma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : ∞-magma) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , _·_) (Y , _*_) (f , _) = Π x ꞉ X , Π y ꞉ X , f (x · y) ＝ (f x) * (f y)

   ρ : (A : ∞-magma) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , _·_) x y = refl

   θ : {X : 𝓤 ̇ } (_·_ _*_ : ∞-magma-structure X)
     → is-equiv (canonical-map ι ρ _·_ _*_)

   θ _·_ _*_ = ((λ p → inverse _ (fe _ _) (λ x → inverse _ (fe _ _) (λ y → p x y)) )
             , (λ x → {!!}))
             , ((λ p → inverse _ (fe _ _) (λ x → inverse _ (fe _ _) (λ y → p x y)))
             , λ x → {!!})

 _≅∞_ : ∞-magma → ∞-magma → 𝓤 ̇
 (X , _·_) ≅∞ (Y , _*_) =
             Σ f ꞉ (X → Y) , is-equiv f
                           × (Π x ꞉ X , Π y ꞉ X , f (x · y) ＝ (f x) * (f y))

 characterization-of-∞-magma : is-univalent 𝓤
                               → (A B : ∞-magma)
                               → (A ＝ B) ≃ (A ≅∞ B)
 characterization-of-∞-magma ua = characterization-of-＝ ua sns-data


 open sip-with-axioms
 
 _≅m_ : Magma → Magma → 𝓤 ̇
 (X , _·_ , _) ≅m (Y , _*_ , _) =
             Σ f ꞉ (X → Y) , is-equiv f
                           × (Π x ꞉ X , Π y ꞉ X , f (x · y) ＝ (f x) * (f y))

 characterization-of-magma-＝ : is-univalent 𝓤 → (A B : Magma) → (A ＝ B) ≃ (A ≅m B)
 characterization-of-magma-＝ ua = characterization-of-＝-with-axioms ua sns-data (λ X s → is-set X) λ X s → being-set-is-prop fe

\end{code}

And finally show that this is a category.

\begin{code}

 lem : (A B : Magma) → (A ≅m B) ≃ (A ≅⟨ MagmaWildcat ⟩ B)
 lem A B = forwards , (backwards , {!!}) , (backwards , {!!})
  where
   forwards : A ≅m B → wildcat-iso-explicit MagmaWildcat A B
   forwards (f , ((g , hs) , (g' , is)) , p) = (f , p) , (g , {!!}) , (to-Σ-＝ ({!inverse _ (fe _ _) (λ x → is x) !} , inverse _ (fe _ _) (λ x → inverse _ (fe _ _) (λ y → {!!})))) , to-Σ-＝ ((inverse _ (fe _ _) (λ x → hs x)) , {!!})

   backwards : wildcat-iso-explicit MagmaWildcat A B → A ≅m B
   backwards ((f , fp) , (g , gp) , lc , rc) = f , ((g , {!!}) , (g , {!!})) , fp

 MagmaCategory : Category (𝓤 ⁺) 𝓤
 MagmaCategory = MagmaPrecategory , is-cat
  where
   is-cat : is-category MagmaPrecategory
   is-cat = {!!}

\end{code}
