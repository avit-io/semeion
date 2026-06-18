{-# OPTIONS --safe --without-K #-}

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  semeion — σημεῖον, il segno.                                          ║
-- ║                                                                        ║
-- ║  Tesi: dare ai segnali osservabili una GEOMETRIA intrinseca tale che   ║
-- ║  la visualizzazione fedele EMERGA come teorema, portando il legame     ║
-- ║  dato↔widget dal regime della stipulazione pura (gusto) a quello       ║
-- ║  dell'emergenza (prova).                                               ║
-- ║                                                                        ║
-- ║  Tre stadi:  Signal ──teorema──▶ Display ──adapter──▶ PanelKind.       ║
-- ║  semeion si ferma a `Display` (la primitiva GEOMETRICA): non importa   ║
-- ║  Penelope, dipende solo da prometea. Il nome Grafana del pannello è    ║
-- ║  l'epifenomeno di un epifenomeno.                                      ║
-- ║                                                                        ║
-- ║  Disciplina (--without-K): l'emergenza è il default. La stipulazione   ║
-- ║  è ammessa SOLO dove la struttura non determina — quarantenata e       ║
-- ║  marcata, come si invoca K localmente in una singola prova, mai come   ║
-- ║  assioma globale.                                                      ║
-- ╚══════════════════════════════════════════════════════════════════════╝

module Semeion.Signal where

open import Data.Nat     using (ℕ; _≤_; z≤n; s≤s)
open import Data.Fin     using (Fin)
open import Data.List    using (List; _∷_; [])
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- ── Il valore bounded è una PROVA, non una config ──────────────────────
-- Un rapporto good/total con good ≤ total. La sua appartenenza a [0,1] è
-- il TEOREMA `num ≤ den`, non un campo `min/max` da indovinare. Non si può
-- marcare bounded qualcosa senza esibire il testimone.
record Ratio : Set where
  constructor mkRatio
  field
    num den : ℕ
    bound   : num ≤ den

-- Esempio: un SLI 1/2. Il `bound` È la dimostrazione 0 ≤ valore ≤ 1.
-- (Una magnitudo unbounded — un rate, una latenza in ms — non ha nulla da
--  mettere qui: per questo finisce in `flow`, non in `ratio`.)
exampleSLI : Ratio
exampleSLI = mkRatio 1 2 (s≤s z≤n)

-- ── Codominio: la struttura intrinseca del valore ──────────────────────
data Codomain : Set where
  flow  : Codomain                 -- magnitudo continua SENZA fondoscala
                                   --   intrinseco: rate, count, latenza-ms
  ratio : Ratio → Codomain         -- continua, bounded [0,1], testimone
                                   --   incorporato: SLI, saturazione, budget
  state : (n : ℕ) → Fin n → Codomain  -- categoriale: n stati, quello corrente

-- ── Indice: scalare singolo o famiglia etichettata ─────────────────────
data Index : Set where
  point      : Index               -- un solo valore
  comparable : Index               -- famiglia su UNA scala condivisa
                                   --   (per-servizio SLI: tutti in [0,1])
  mixed      : Index               -- famiglia su scale eterogenee (unità diverse)

record Signal : Set where          -- NB: nessun campo `intent`. L'intento
  constructor mkSignal             --     è il K locale, non un asse del segnale.
  field
    cod : Codomain
    idx : Index

-- ── Display: la primitiva GEOMETRICA, nominata da cos'È, non da Grafana ─
data Display : Set where
  arc        : Display   -- un valore dentro un intervallo noto (→ gauge)
  bars       : Display   -- N valori comparabili su una scala (→ bargauge)
  number     : Display   -- una magnitudo senza fondoscala (→ stat)
  line       : Display   -- una traiettoria continua nel tempo (→ timeseries)
  stateBands : Display   -- una traiettoria categoriale (→ status-history)
  grid       : Display   -- una famiglia non comparabile (→ table)

-- ── L'onestà è NEL TIPO ────────────────────────────────────────────────
-- Il codominio di `displayAt` testimonia se la scelta è emersa o no.
data Faithful : Set where
  forced          : Display → Faithful         -- emerge: unico fedele
  underdetermined : List Display → Faithful     -- la struttura non forza:
                                                --   menu onesto, serve un fiat

-- ── L'intento: l'UNICA stipulazione (il K locale) ──────────────────────
-- Non vive nel segnale. È la domanda dell'operatore, pagata al sito d'uso.
data Intent : Set where
  now      : Intent   -- "quanto vale adesso"
  overTime : Intent   -- "che traiettoria ha"

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  Il teorema centrale come funzione totale.                            ║
-- ║  Pagato l'intento, la STRUTTURA forza il display — tranne UNA cella.  ║
-- ╚══════════════════════════════════════════════════════════════════════╝
displayAt : Intent → Signal → Faithful
-- overTime: la continuità del codominio forza linea vs bande. Una linea
-- tracciata fra FAIL e OK sarebbe una menzogna geometrica ⇒ stateBands.
displayAt overTime (mkSignal flow        _)          = forced line
displayAt overTime (mkSignal (ratio _)   _)          = forced line
displayAt overTime (mkSignal (state _ _) _)          = forced stateBands
-- now, bounded: l'intervallo intrinseco È l'arco; N comparabili sono barre.
displayAt now (mkSignal (ratio _)   point)      = forced arc
displayAt now (mkSignal (ratio _)   comparable) = forced bars
displayAt now (mkSignal (ratio _)   mixed)      = forced bars   -- i ratio
                                              -- condividono [0,1]: sempre comparabili
-- now, unbounded: niente fondoscala ⇒ numero nudo (un arco avrebbe estremi fiat).
displayAt now (mkSignal flow        point)      = forced number
displayAt now (mkSignal flow        mixed)      = forced grid    -- unità eterogenee
-- L'UNICA cella sottodeterminata: magnitudi unbounded comparabili, adesso.
-- Lista di stat vs tabella è gusto. La struttura NON sceglie ⇒ menu.
displayAt now (mkSignal flow        comparable) = underdetermined (number ∷ grid ∷ [])
-- now, categoriale: stato corrente come badge / tabella di stati.
displayAt now (mkSignal (state _ _) point)      = forced number
displayAt now (mkSignal (state _ _) comparable) = forced grid
displayAt now (mkSignal (state _ _) mixed)      = forced grid

-- Senza pagare l'intento (senza il K), lo spread irriducibile del segnale.
viz : Signal → List Display
viz s = collect (displayAt now s) ++ᵈ collect (displayAt overTime s)
  where
    collect : Faithful → List Display
    collect (forced d)           = d ∷ []
    collect (underdetermined ds) = ds
    _++ᵈ_ : List Display → List Display → List Display
    []       ++ᵈ ys = ys
    (x ∷ xs) ++ᵈ ys = x ∷ (xs ++ᵈ ys)

-- ╔══════════════════════════════════════════════════════════════════════╗
-- ║  TEOREMI                                                              ║
-- ╚══════════════════════════════════════════════════════════════════════╝

-- ── ratio/SLI: la visualizzazione EMERGE, dato l'intento (regime 1) ────
-- "scalare → gauge" non è più un fiat: bounded + point + now ⇒ arc, provato.
sliNow : ∀ (r : Ratio) → displayAt now (mkSignal (ratio r) point) ≡ forced arc
sliNow _ = refl

sliTrend : ∀ (r : Ratio) → displayAt overTime (mkSignal (ratio r) point) ≡ forced line
sliTrend _ = refl

-- Famiglia di SLI per-servizio (tutti in [0,1], comparabili) ⇒ barre.
sliFamily : ∀ (r : Ratio) → displayAt now (mkSignal (ratio r) comparable) ≡ forced bars
sliFamily _ = refl

-- ── Rifiuto onesto: una magnitudo unbounded NON è una gauge ────────────
-- Latenza p99 / rate / count: niente fondoscala. semeion RIFIUTA l'arco
-- (in Grafana è il peccato del fondoscala inventato).
latencyIsNumber : displayAt now (mkSignal flow point) ≡ forced number
latencyIsNumber = refl

latencyNotArc : displayAt now (mkSignal flow point) ≢ forced arc
latencyNotArc ()

-- ── Pagare overTime forza SEMPRE: nessun residuo su quel ramo ──────────
overTimeAlwaysForced : ∀ (s : Signal) → ∃[ d ] displayAt overTime s ≡ forced d
overTimeAlwaysForced (mkSignal flow        _) = line       , refl
overTimeAlwaysForced (mkSignal (ratio _)   _) = line       , refl
overTimeAlwaysForced (mkSignal (state _ _) _) = stateBands , refl

-- ── L'UNICA cella sottodeterminata, esibita (onestà nel tipo) ──────────
-- Non la mascheriamo con una scelta: il tipo dice `underdetermined`.
flowFamilyUnderdetermined :
  displayAt now (mkSignal flow comparable) ≡ underdetermined (number ∷ grid ∷ [])
flowFamilyUnderdetermined = refl
