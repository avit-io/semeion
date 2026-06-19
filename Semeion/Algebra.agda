{-# OPTIONS --safe --without-K #-}

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  Algebra dei segnali — le TRASFORMAZIONI, non solo le foglie.          ║
-- ║                                                                        ║
-- ║  semeion modella la natura di un segnale; un segnale però si compone   ║
-- ║  (Prometheus: sum/avg/topk/…). La domanda di tipo: quali testimoni     ║
-- ║  SOPRAVVIVONO a una composizione? La risposta deve EMERGERE, non       ║
-- ║  stipularsi — come per le foglie.                                      ║
-- ║                                                                        ║
-- ║  Primo frammento: l'ADDIZIONE. Il risultato chiave è regime 1: ora     ║
-- ║  che `ratio` porta un `Bounded [lo,hi]` qualsiasi, la somma di due     ║
-- ║  bounded È bounded, e il suo fondoscala [lo₁+lo₂, hi₁+hi₂] EMERGE       ║
-- ║  dalla monotonicità di + su ℚ. "Sommare due SLI non dà un SLI [0,1]"   ║
-- ║  diventa un teorema: il tetto è 1+1, non 1 — dimostrato, non inventato.║
-- ╚══════════════════════════════════════════════════════════════════════╝

module Semeion.Algebra where

open import Semeion.Signal
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _≤_; _≤?_; nonNegative)
import      Data.Rational.Properties as ℚ
open import Data.Nat using (ℕ; _⊓_)
import      Data.Nat as ℕ
open import Data.Nat.Properties using (m⊓n≤n; m≥n⇒m⊓n≡n)
open import Data.Fin using (Fin; inject≤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Relation.Nullary.Decidable using (from-yes)

-- ── I bound si COMPONGONO sotto la somma (regime 1) ────────────────────
-- La somma di due valori bounded è bounded, e i suoi estremi sono la somma
-- degli estremi: `lo₁+lo₂ ≤ v₁+v₂ ≤ hi₁+hi₂`. Il nuovo fondoscala NON si
-- stipula: i due testimoni emergono da `+-mono-≤` (la monotonicità di + su
-- ℚ). È il `m≤m+n` dell'SLI portato al livello delle TRASFORMAZIONI.
_⊕_ : Bounded → Bounded → Bounded
b₁ ⊕ b₂ = mkBounded (Bounded.lo b₁ + Bounded.lo b₂)
                    (Bounded.hi b₁ + Bounded.hi b₂)
                    (Bounded.v  b₁ + Bounded.v  b₂)
                    (ℚ.+-mono-≤ (Bounded.lo≤v b₁) (Bounded.lo≤v b₂))
                    (ℚ.+-mono-≤ (Bounded.v≤hi b₁) (Bounded.v≤hi b₂))

-- ── Scalare per una costante non-negativa preserva il bound ───────────
-- Moltiplicare lo/hi/v per `q ≥ 0` mantiene l'ordine (`*-monoˡ-≤-nonNeg`):
-- i testimoni si trasportano. Serve alla media, che è una somma SCALATA.
scaleNonNeg : (q : ℚ) → 0ℚ ≤ q → Bounded → Bounded
scaleNonNeg q 0≤q b =
  mkBounded (q * Bounded.lo b) (q * Bounded.hi b) (q * Bounded.v b)
            (ℚ.*-monoˡ-≤-nonNeg q ⦃ nonNegative 0≤q ⦄ (Bounded.lo≤v b))
            (ℚ.*-monoˡ-≤-nonNeg q ⦃ nonNegative 0≤q ⦄ (Bounded.v≤hi b))

-- ── La media: somma scalata di ½. Resta nello SCAFO CONVESSO ───────────
-- A differenza di `⊕`, la media NON sfora: media di due bounded sta fra i
-- loro estremi. È il duale onesto della somma — stessa algebra, fondoscala
-- che si CONTRAE invece di sommarsi.
private
  0≤½ : 0ℚ ≤ ½
  0≤½ = from-yes (0ℚ ≤? ½)

avg : Bounded → Bounded → Bounded
avg b₁ b₂ = scaleNonNeg ½ 0≤½ (b₁ ⊕ b₂)

-- ── Frazione numerica: cosa si PUÒ sommare (i categoriali no) ──────────
-- Sommare due `state` (OK + WARN?) è un errore di categoria: non esiste
-- `Numeric (state …)`. L'addizione è offerta SOLO sul frammento numerico,
-- e lì è chiusa — l'onestà è nel tipo, non in un catch-all che mente.
data Numeric : Codomain → Set where
  num-flow  : Numeric flow
  num-ratio : ∀ b → Numeric (ratio b)

-- La somma di due codomini numerici è numerica e CHIUSA. Due bounded: i
-- bound si compongono (`⊕`). Appena un `flow` entra, il bound è PERSO — una
-- magnitudo unbounded sommata a qualsiasi cosa resta unbounded ⇒ `flow`.
-- L'algebra NON inventa un fondoscala dove un operando non ne ha.
addCod : ∀ {c₁ c₂} → Numeric c₁ → Numeric c₂ → Codomain
addCod (num-ratio b₁) (num-ratio b₂) = ratio (b₁ ⊕ b₂)
addCod _              _              = flow

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  TEOREMI                                                              ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- Due bounded ⇒ i bound si compongono (il fondoscala non è stipulato).
addRatio : ∀ b₁ b₂ → addCod (num-ratio b₁) (num-ratio b₂) ≡ ratio (b₁ ⊕ b₂)
addRatio _ _ = refl

-- Un `flow` (a sinistra o a destra) perde il bound: nessun fondoscala inventato.
addFlowˡ : ∀ {c} (n : Numeric c) → addCod num-flow n ≡ flow
addFlowˡ num-flow      = refl
addFlowˡ (num-ratio _) = refl

addFlowʳ : ∀ {c} (n : Numeric c) → addCod n num-flow ≡ flow
addFlowʳ num-flow      = refl
addFlowʳ (num-ratio _) = refl

-- ── "Sommare due ratio NON dà un ratio [0,1]" come TEOREMA ─────────────
-- Il tetto della somma di due unitari è 1+1, non 1: l'arco emerge ancora,
-- ma il suo fondoscala [0,2] è DIMOSTRATO (i bound si sommano via `⊕`), non
-- un fiat. La forma sopravvive alla composizione; il dominio si trasforma,
-- onestamente.
sumUnitsHi : ∀ (b₁ b₂ : Bounded)
  → Bounded.hi b₁ ≡ 1ℚ → Bounded.hi b₂ ≡ 1ℚ
  → Bounded.hi (b₁ ⊕ b₂) ≡ 1ℚ + 1ℚ
sumUnitsHi _ _ e₁ e₂ = cong₂ _+_ e₁ e₂

-- ── …la MEDIA invece NON sfora: il contrasto onesto sum/avg ────────────
-- Il tetto della media di due unitari è di nuovo 1: la media resta nell'unità
-- [0,1] (scafo convesso), mentre la somma ne esce. Stessa algebra, due regole
-- di tipo diverse — entrambe TEOREMI, nessuna stipulata.
avgUnitsHi : ∀ (b₁ b₂ : Bounded)
  → Bounded.hi b₁ ≡ 1ℚ → Bounded.hi b₂ ≡ 1ℚ
  → Bounded.hi (avg b₁ b₂) ≡ 1ℚ
avgUnitsHi _ _ refl refl = refl

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  topk — il RANKING presuppone la comparabilità                        ║
-- ╚══════════════════════════════════════════════════════════════════════╝
-- `topk(k)` seleziona le k serie di valore più alto in una famiglia. Ma
-- ordinare presuppone una SCALA COMUNE: rankare byte/s contro secondi è un
-- errore di categoria. Per questo topk è offerto SOLO su una famiglia
-- `comparable` (dimensioni provate uguali) — `mixed` e `point` non sono
-- `Rankable`, esattamente come `state` non è `Numeric`. La precondizione
-- emerge da "cosa significa ordinare", non si stipula.
data Rankable : Index → Set where
  rank-comparable : ∀ n ds (p : AllEqual ds) → Rankable (comparable n ds p)

-- Restrizione di una famiglia a un sotto-indice: la dimensione condivisa
-- SOPRAVVIVE (ogni sottoinsieme di una famiglia all-equal è all-equal).
private
  restrict : ∀ {m n} → m ℕ.≤ n → (Fin n → Dim) → (Fin m → Dim)
  restrict m≤n ds i = ds (inject≤ i m≤n)

  restrict-AllEqual : ∀ {m n} (m≤n : m ℕ.≤ n) {ds : Fin n → Dim}
    → AllEqual ds → AllEqual (restrict m≤n ds)
  restrict-AllEqual m≤n p i j = p (inject≤ i m≤n) (inject≤ j m≤n)

-- L'indice dopo topk: una famiglia di taglia `k ⊓ n` con la STESSA dimensione
-- (comparabilità preservata). Quali k serie è dato a runtime — il tipo cattura
-- la TRASFORMAZIONE (taglia ↓, scala invariata), non la selezione.
topkIdx : ℕ → ∀ {i} → Rankable i → Index
topkIdx k (rank-comparable n ds p) =
  comparable (k ⊓ n) (restrict (m⊓n≤n k n) ds) (restrict-AllEqual (m⊓n≤n k n) p)

-- topk sul segnale: preserva codominio e temporalità, trasforma l'indice.
topk : ℕ → (s : Signal) → Rankable (Signal.idx s) → Signal
topk k s r = mkSignal (Signal.cod s) (topkIdx k r) (Signal.tmp s)

-- Taglia della famiglia (per enunciare i teoremi sull'indice).
famSize : Index → ℕ
famSize point            = 1
famSize (comparable n _ _) = n
famSize (mixed n _ _)      = n

-- ── TEOREMI ────────────────────────────────────────────────────────────

-- Marquee: ordinare una famiglia INCOMPARABILE è un errore di tipo. Niente
-- `Rankable (mixed …)` — il duale, sul ranking, di `state ∉ Numeric`.
mixedNotRankable : ∀ {n ds} {¬p : ¬ AllEqual ds} → ¬ Rankable (mixed n ds ¬p)
mixedNotRankable ()

-- Anche un singolo valore non è una famiglia da ordinare.
pointNotRankable : ¬ Rankable point
pointNotRankable ()

-- topk preserva il codominio (la forma del valore non cambia) e la temporalità.
topkCod : ∀ k (s : Signal) (r : Rankable (Signal.idx s)) → Signal.cod (topk k s r) ≡ Signal.cod s
topkCod _ _ _ = refl

topkTmp : ∀ k (s : Signal) (r : Rankable (Signal.idx s)) → Signal.tmp (topk k s r) ≡ Signal.tmp s
topkTmp _ _ _ = refl

-- La taglia risultante è k ⊓ n (né più di k, né più della famiglia).
topkSize : ∀ k n ds (p : AllEqual ds)
  → famSize (topkIdx k (rank-comparable n ds p)) ≡ k ⊓ n
topkSize _ _ _ _ = refl

-- k ≥ n: topk restituisce l'INTERA famiglia (k ⊓ n ≡ n).
topkAll : ∀ k n ds (p : AllEqual ds) → n ℕ.≤ k
  → famSize (topkIdx k (rank-comparable n ds p)) ≡ n
topkAll _ _ _ _ n≤k = m≥n⇒m⊓n≡n n≤k

-- topk è CHIUSO: il risultato è di nuovo una famiglia rankable (ri-ordinabile).
topkRankable : ∀ k {i} (r : Rankable i) → Rankable (topkIdx k r)
topkRankable k (rank-comparable n ds p) =
  rank-comparable (k ⊓ n) (restrict (m⊓n≤n k n) ds) (restrict-AllEqual (m⊓n≤n k n) p)

-- Payoff: topk non cambia COME si legge il segnale. Una famiglia comparabile
-- di ratio resta `bars` (il widget sopravvive alla selezione).
topkRatioStillBars : ∀ k b n ds (p : AllEqual ds) (t : Temporal)
  → displayAt now
      (topk k (mkSignal (ratio b) (comparable n ds p) t) (rank-comparable n ds p))
      ≡ forced bars
topkRatioStillBars _ _ _ _ _ _ = refl
