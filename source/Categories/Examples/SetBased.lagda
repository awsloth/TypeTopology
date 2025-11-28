Anna Williams, 27 November 2025

Univalence for Set based structures

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Categories.Type renaming (id to c-id)
open import MLTT.Spartan hiding (_∘_)
open import UF.Base
open import UF.Equiv hiding (_≅⟨_⟩_)
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SIP
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.Univalence

module Categories.Examples.SetBased where

\end{code}

\begin{code}

module _ {S : 𝓤 ̇  → 𝓥 ̇ }
         {P : (a b : Σ S)
              (f : (pr₁ a) → (pr₁ b))
            → 𝓦 ̇ }
         (id-property : {a : Σ S} → P a a id)
         (comp-property : {a b c : Σ S}
                          (f : Σ (P b c))
                          (g : Σ (P a b))
                        → P a c (λ x → (pr₁ f) ((pr₁ g) x)))
         (left-id-prop : {a b : Σ S}
                    (f : Σ (P a b))
                  → comp-property ((λ x → x) , id-property) f ＝ (pr₂ f))
         (right-id-prop : {a b : Σ S}
                    (f : Σ (P a b))
                  → comp-property f ((λ x → x) , id-property) ＝ (pr₂ f))
         (assoc-prop : {a b c d : Σ S}
                       (f : Σ (P a b))
                       (g : Σ (P b c))
                       (h : Σ (P c d))
                     → comp-property (h .pr₁ , h .pr₂)
                        ((λ x → g .pr₁ (f .pr₁ x)) ,
                        comp-property (g .pr₁ , g .pr₂) (f .pr₁ , f .pr₂))
                        ＝
                        comp-property
                         ((λ x → h .pr₁ (g .pr₁ x)) ,
                          comp-property (h .pr₁ , h .pr₂) (g .pr₁ , g .pr₂))
                           (f .pr₁ , f .pr₂))
         (inv-is-hom : (a b : Σ S)
                       (f : (pr₁ a) → (pr₁ b))
                       (e : is-equiv f)
                       (pf : P a b f)
                     → P b a (inverse f e))
         (P-is-prop : (a b : Σ S)
                   → (f : (pr₁ a) → (pr₁ b))
                   → is-prop (P a b f))
         (underlying-is-set : (a : Σ S) → is-set (pr₁ a))
         (prop-to-id : {X : 𝓤 ̇ }
                       (s t : S X)
                     → P (X , s) (X , t) (λ x → x) → s ＝ t)
         (prop-to-id-property : {X : 𝓤 ̇ }
                                (s t : S X)
                                (x : P (X , s) (X , t) id)
                              → transport (λ v → P (X , s) (X , v) id) (prop-to-id s t x) id-property ＝ x)
         (fe : Fun-Ext)
         (ua : is-univalent 𝓤)
 where

 inv-eq : {a b : 𝓤 ̇ }
          {f : a → b}
          (e : is-equiv f)
        → pr₁ (pr₁ e) ＝ pr₁ (pr₂ e)
 inv-eq {_} {_} {f}
        ((g , gp) , (g' , gp')) = inverse _ (fe _ _)
                                  λ x → g x          ＝⟨ (gp' (g x))⁻¹ ⟩
                                        g' (f (g x)) ＝⟨ ap g' (gp x) ⟩
                                        g' x         ∎

 gen-wildcat : WildCategory ((𝓤 ⁺) ⊔ 𝓥) (𝓤 ⊔ 𝓦)
 gen-wildcat = wildcat-make (Σ S)
                            (λ a b → Σ f ꞉ ((pr₁ a) → (pr₁ b)) , P a b f)
                            (id , id-property)
                            (λ (f , pf) (g , pg) → (λ x → f (g x)) , comp-property (f , pf) (g , pg))
                            (λ f → to-Σ-＝ (refl , left-id-prop f))
                            (λ f → to-Σ-＝ (refl , right-id-prop f))
                            λ f g h → to-Σ-＝ (refl , assoc-prop f g h)

 gen-precat : Precategory ((𝓤 ⁺) ⊔ 𝓥) (𝓤 ⊔ 𝓦)
 gen-precat = gen-wildcat , λ a b → Σ-is-set (Π-is-set fe (λ _ → underlying-is-set b)) (λ f → props-are-sets (P-is-prop a b f))

 open sip

 gen-sns-data : SNS S 𝓦
 gen-sns-data = ι , ρ , θ
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓦 ̇
   ι A B (f , _) = P A B f

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ A = id-property

   h : {X : 𝓤 ̇ }
       (s t : S X)
     → ι (X , s) (X , t) (≃-refl X) ◁ (s ＝ t)
   h {X} s t = toid , (fromid , retract)
    where
     toid : s ＝ t → ι (X , s) (X , t) (≃-refl _)
     toid = λ p → transport (λ v → P (X , s) (X , v) id) p id-property

     fromid : ι (X , s) (X , t) (≃-refl X) → s ＝ t
     fromid = prop-to-id s t

     retract : (λ x → toid (fromid x)) ∼ (λ x → x)
     retract = prop-to-id-property s t

   θ : {X : 𝓤 ̇ }
      (s t : S X)
    → is-equiv (canonical-map ι ρ s t)
   θ = canonical-map-equiv-criterion' ι ρ h

 sns-equiv-iso : (A B : Σ S)
               → (A ≃[ gen-sns-data ] B) ≃ (A ≅⟨ gen-wildcat ⟩ B)
 sns-equiv-iso A B = toiso , (fromiso , left) , (fromiso , right)
  where
   toiso : (A ≃[ gen-sns-data ] B) → (A ≅⟨ gen-wildcat ⟩ B)
   toiso (f , e@((g , gp) , (g' , gp')) , fp)
          = (f , fp)
          , (g , inv-is-hom A B f e fp)
          , to-subtype-＝ (λ iden → P-is-prop A A iden) (inverse _ (fe _ _) (inverses-are-retractions f e))
          , to-subtype-＝ (λ iden → P-is-prop B B iden) (inverse _ (fe _ _) gp)

   fromiso : (A ≅⟨ gen-wildcat ⟩ B) → (A ≃[ gen-sns-data ] B)
   fromiso ((f , fp) , (g , gp) , lg , rg) = f
                                           , ((g , λ x → ap (λ - → - x) (ap pr₁ rg)) , (g , λ x → ap (λ - → - x) (ap pr₁ lg)))
                                           , fp

   left : (λ x → toiso (fromiso x)) ∼ (λ x → x)
   left ((f , fp) , (g , gp) , lg , rg) = to-Σ-＝ (refl , (to-Σ-＝ (to-Σ-＝ (refl , P-is-prop B A g _ _) , (to-×-＝ (hom-is-set {{gen-precat}} _ lg) (hom-is-set {{gen-precat}} _ rg)))))

   right : (λ x → fromiso (toiso x)) ∼ (λ x → x)
   right (f , e@((g , gp) , (g' , gp')) , fp) = to-Σ-＝ (refl , to-×-＝ (to-×-＝ (to-subtype-＝ (λ h → Π-is-prop fe λ x a b → underlying-is-set B _ _) refl) (to-subtype-＝ (λ h → Π-is-prop fe λ x a b → underlying-is-set A _ _) (inv-eq e))) refl)


 characterization-of-gen-＝ : (A B : Σ S)
                            → (A ＝ B) ≃ (A ≅⟨ gen-wildcat ⟩ B)
 characterization-of-gen-＝ A B = ≃-comp
                                  (characterization-of-＝ ua gen-sns-data A B)
                                  (sns-equiv-iso A B)

 gen-category : Category ((𝓤 ⁺) ⊔ 𝓥) (𝓤 ⊔ 𝓦)
 gen-category = gen-precat , is-cat
  where
   eq : (a b : Σ S)
      → id-to-iso {{gen-wildcat}} a b
      ∼ ⌜ characterization-of-gen-＝ a b ⌝
   eq a b refl = to-Σ-＝ (refl , is-iso-equality)
    where
     inverse-eq = to-subtype-＝ (P-is-prop a a) refl
     left-inv = hom-is-set {{gen-precat}} {a} {a} _ _
     right-inv = hom-is-set {{gen-precat}} {a} {a} _ _
     is-iso-equality = to-Σ-＝ (inverse-eq , to-×-＝ left-inv right-inv)

   is-cat : is-category gen-precat
   is-cat a b = equiv-closed-under-∼ ⌜ characterization-of-gen-＝ a b ⌝ (id-to-iso {{gen-wildcat}} a b) (pr₂ (characterization-of-gen-＝ a b)) (eq a b)
   
