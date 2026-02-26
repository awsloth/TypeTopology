Anna Williams, 13 November 2025

The Category of Magmas

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import Categories.Wild
open import Categories.Pre 
open import Categories.Univalent
open import Categories.Notation.Wild hiding (inverse ; ⌜_⌝)
open import MLTT.Spartan
open import UF.Base
open import UF.Equiv hiding (_≅_)
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.Examples.Magma where

module _ {𝓤 : Universe} (fe : Fun-Ext) where
 Magma : 𝓤 ⁺ ̇
 Magma = Σ X ꞉ 𝓤 ̇ , (X → X → X) × is-set X

 MagmaWildcat : WildCategory (𝓤 ⁺) 𝓤
 MagmaWildcat = wildcategory Magma
                             magma-hom
                             (λ {a} → magma-id {a})
                             (λ {a} {b} {c} → magma-comp {a} {b} {c})
                             (λ {a} {b} → magma-l-id {a} {b})
                             (λ {a} {b} → magma-r-id {a} {b})
                             λ {a} {b} {c} {d} → magma-assoc {a} {b} {c} {d}
  where
   magma-hom : (a b : Magma) → 𝓤 ̇
   magma-hom (X , _·_ , _)
             (Y , _*_ , _)
    = Σ f ꞉ (X → Y) , ((x y : X) → f (x · y) ＝ f x * f y)

   magma-id : {a : Magma} → magma-hom a a
   magma-id = id , λ x y → refl

   magma-comp : {a b c : Magma}
              → magma-hom b c
              → magma-hom a b
              → magma-hom a c
   magma-comp {X , _·_ , _}
              {Y , _*_ , _}
              {Z , _∙_ , _}
              (f , fp)
              (g , gp) = f ∘ g , property-comp
    where
     property-comp : (x y : X) → (f ∘ g) (x · y) ＝ (f ∘ g) x ∙ (f ∘ g) y
     property-comp x y = (f ∘ g) (x · y)       ＝⟨ ap f (gp x y) ⟩
                         f (g x * g y)         ＝⟨ fp (g x) (g y) ⟩
                         (f ∘ g) x ∙ (f ∘ g) y ∎

   magma-l-id : {a b : Magma}
                (f : magma-hom a b)
              → magma-comp {a} {b} {b} (magma-id {b}) f ＝ f
   magma-l-id {_} {_ , _ , sY} (f , pf) = to-Σ-＝ (refl , property-equality)
    where
     property-equality = dfunext fe
                          λ x → dfunext fe
                           λ y → sY _ _

   magma-r-id : {a b : Magma}
                (f : magma-hom a b)
              → magma-comp {a} {a} {b} f (magma-id {a}) ＝ f
   magma-r-id {_} {_ , _ , sY} (f , pf) = to-Σ-＝ (refl , property-equality)
    where
     property-equality = dfunext fe
                          λ x → dfunext fe
                           λ y → sY _ _

   magma-assoc : {a b c d : Magma}
                 (f : magma-hom a b)
                 (g : magma-hom b c)
                 (h : magma-hom c d)
               → magma-comp {a} {c} {d} h (magma-comp {a} {b} {c} g f)
               ＝ magma-comp {a} {b} {d} (magma-comp {b} {c} {d} h g) f
   magma-assoc {_} {_} {_} {_ , _ , S}
               (f , pf) (g , pg) (h , ph) = to-Σ-＝ (refl , property-equality)
    where
     property-equality = dfunext fe
                          λ x → dfunext fe
                           λ y → S _ _

 open WildCategoryNotation MagmaWildcat

\end{code}

We now show that this is a precategory

\begin{code}

 MagmaPrecategory : Precategory (𝓤 ⁺) 𝓤
 MagmaPrecategory = MagmaWildcat , is-pre
  where
   is-pre : is-precategory MagmaWildcat
   is-pre (_ , _ , sX) (_ , _ , sY) = Σ-is-set (Π-is-set fe (λ _ → sY))
                                                λ f → Π₂-is-set fe
                                                  λ x y → props-are-sets sY

\end{code}

We show that Magmas have univalence

\begin{code}

 open sip

 Magma-structure : 𝓤 ̇  → 𝓤 ̇ 
 Magma-structure X = (X → X → X) × is-set X


 Magma-hom-pres : (a b : Magma) (f : pr₁ a → pr₁ b) → 𝓤 ̇
 Magma-hom-pres (X , _·_ , _)
                (Y , _*_ , _) f = ((x y : X) → f (x · y) ＝ (f x) * (f y))

 sns-data : SNS Magma-structure 𝓤
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Magma) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ̇
   ι (X , _·_ , _)
     (Y , _*_ , _)
     (f , _) = ((x y : X) → f (x · y) ＝ (f x) * (f y))

   ρ : (A : Magma) → ι A A (≃-refl ⟨ A ⟩)
   ρ A x y = refl

   h : {X : 𝓤 ̇ }
       (s t : Magma-structure X)
     → ι (X , s) (X , t) (≃-refl _) ◁ (s ＝ t)
   h {X} (_·_ , sX) (_*_ , sX') = forwards , (backwards , retract)
    where
     forwards = (λ p x y → ap (λ - → - x y) (ap pr₁ p))

     backwards = λ p → to-×-＝ (dfunext fe
                                λ x → dfunext fe
                                 λ y → p x y)
                               (being-set-is-prop fe sX sX')

     retract = λ i → dfunext fe
                      λ x → dfunext fe
                       λ y → sX _ _


   θ : {X : 𝓤 ̇ }
       (a b : Magma-structure X)
     → is-equiv (canonical-map ι ρ a b)

   θ {X} = canonical-map-equiv-criterion' ι ρ h

 inverse' : {a b : 𝓤 ̇ }
            {f : a → b}
            (e : is-equiv f)
          → (b → a)
 inverse' = pr₁ ∘ pr₂

 inv-eq : {a b : 𝓤 ̇ }
          {f : a → b}
          (e : is-equiv f)
        → inverse f e  ＝ inverse' e
 inv-eq {_} {_} {f}
        ((g , gp) , (g' , gp')) = inverse _ (fe _ _)
                                  λ x → g x          ＝⟨ (gp' (g x))⁻¹ ⟩
                                        g' (f (g x)) ＝⟨ ap g' (gp x) ⟩
                                        g' x         ∎

 sns-equiv-iso : (A B : Magma)
               → (A ≃[ sns-data ] B) ≃ (A ≅ B)
 sns-equiv-iso A@(a , _·_ , sA) B@(b , _*_ , sB) = toiso
                                                 , (fromiso , left)
                                                 , (fromiso , right)
  where
   toiso : A ≃[ sns-data ] B → A ≅ B
   toiso (f , e@((g , gp) , (g' , gp')) , fp)
         = (f , fp)
         , (g , hom-prop-for-inv)
         , (to-subtype-＝ left-prop (inverse _ (fe _ _) left-inv))
         , to-subtype-＝ right-prop (inverse _ (fe _ _) gp)
    where
     hom-prop-for-inv : (x y : b) → g (x * y) ＝ (g x · g y)
     hom-prop-for-inv x y = g (x * y)             ＝⟨ i ⟩
                            g (f (g x) * y)       ＝⟨ ii ⟩
                            g (f (g x) * f (g y)) ＝⟨ iii ⟩
                            g (f (g x · g y))     ＝⟨ iv ⟩
                            g x · g y             ∎
      where
       i   = ap (λ - → g (- * y)) (gp x)⁻¹
       ii  = ap (λ - → g (f (g x) * -)) (gp y)⁻¹
       iii = ap g (fp (g x) (g y))⁻¹
       iv  = g (f (g x · g y)) ＝⟨ ap _ (inv-eq e) ⟩
             g' (f (g x · g y)) ＝⟨ gp' (g x · g y) ⟩
             g x · g y ∎

     left-prop = (λ _ → Π₂-is-prop fe (λ _ _ → sA))
     right-prop = (λ _ → Π₂-is-prop fe (λ _ _ → sB))
     
     left-inv : (λ x → g (f x)) ∼ (λ x → x)
     left-inv x = g (f x)  ＝⟨ ap (λ - → - (f x)) (inv-eq e) ⟩
                  g' (f x) ＝⟨ gp' x ⟩
                  x ∎
     
   fromiso : A ≅ B → A ≃[ sns-data ] B
   fromiso ((f , fp) , (g , gp) , lg , rg) = f
                                             , ((g , λ x → ap (λ - → - x)
                                                              (ap pr₁ rg))
                                               , g , λ x → ap (λ - → - x)
                                                              (ap pr₁ lg))
                                             , fp

   left : (λ x → toiso (fromiso x)) ∼ (λ x → x)
   left ((f , fp) , (g , gp) , lg , rg) = to-Σ-＝ (refl , is-iso-eq)
    where
     inv-eq' = (to-subtype-＝ (λ _ → Π₂-is-prop fe λ _ _ → sA) refl)

     left-id-eq = hom-is-set MagmaPrecategory {A} {A} _ _
     right-id-eq = hom-is-set MagmaPrecategory {B} {B} _ _
     axiom-equalities = to-×-＝ left-id-eq right-id-eq
     is-iso-eq = to-Σ-＝ (inv-eq' , axiom-equalities)
   
   right : (λ x → fromiso (toiso x)) ∼ (λ x → x)
   right (f , e@((g , gp) , (g' , gp')) , fp) = to-Σ-＝ (refl
                                                     , (to-×-＝ equiv-eq refl))
    where
     equiv-eq = (to-×-＝
                 (to-subtype-＝ (λ p → Π-is-prop fe λ y → sB) refl)
                 (to-subtype-＝ (λ p → Π-is-prop fe λ y → sA) (inv-eq e)))

 characterization-of-magma-＝ : is-univalent 𝓤
                             → (A B : Magma)
                             → (A ＝ B) ≃ (A ≅ B)
 characterization-of-magma-＝ ua A B = ≃-comp
                                       (characterization-of-＝ ua sns-data A B)
                                       (sns-equiv-iso A B)

\end{code}

And finally show that this is a category.

\begin{code}

 MagmaCategory : is-univalent 𝓤 → Category (𝓤 ⁺) 𝓤
 MagmaCategory ua = MagmaPrecategory , is-cat
  where
   eq : (A B : Magma)
      → id-to-iso A B
      ∼ ⌜ characterization-of-magma-＝ ua A B ⌝
   eq A@(a , _·_ , sA) B@(b , _*_ , sB) refl = to-Σ-＝ (refl , is-iso-equality)
    where
     inv-eq' = to-subtype-＝ (λ f → Π₂-is-prop fe (λ _ _ → sB)) refl
     left-inv = hom-is-set MagmaPrecategory {A} {A} _ _
     right-inv = hom-is-set MagmaPrecategory {A} {A} _ _
     is-iso-equality = to-Σ-＝ (inv-eq' , to-×-＝ left-inv right-inv)

   is-cat : is-category MagmaPrecategory
   is-cat A B = equiv-closed-under-∼ ⌜ characterization-of-magma-＝ ua A B ⌝
                                     (id-to-iso A B)
                                     (pr₂ (characterization-of-magma-＝ ua A B))
                                     (eq A B)

\end{code}
