# semeion

<p align="center">
  <img src="logo.svg" width="160" alt="semeion — l'occhio dell'àugure: l'iride è un arco, la lancetta forzata sul valore in [0,1]"/>
</p>

> *Il segno non si interpreta a piacere — si legge. La forma fedele di un
> segnale non si stipula: emerge.*

Intrinsic geometry of SRE signals in Agda — la struttura semantica di un
segnale (dimensionalità, bounds, temporalità, comparabilità) tale che la
**visualizzazione fedele EMERGA come teorema**. A valle alimenta Penelope
(che resta il render): semeion produce la scelta *già dimostrata*, non tocca
JSON.

---

## Il problema che ereditiamo

In Penelope il legame dato↔widget è **sottodeterminato**: il tipo di pannello
(`stat`/`gauge`/`bargauge` per uno scalare) è scelto a mano. Distinguiamo tre
regimi epistemici:

1. **emergente** (teorema) — proprietà intrinseca di una struttura: la
   disgiunzione delle foglie di un tiling guillotine non si stipula, si
   *dimostra*.
2. **fedeltà** (stipulazione vincolata dal reale) — modella un fatto di
   Grafana (`stat` legge uno scalare; `alias` è morto in schema ≥39).
   Falsificabile.
3. **stipulazione pura** (gusto) — nessun oggetto da cui emerga, nessun fatto
   che la disciplini: "scalare → gauge". Fiat.

La scelta del widget oggi cade nel **regime 3**. Spacciarla per prova è
disonesto.

### La diagnosi precisa

Guarda `Examples/SLO.agda` di Penelope — lì il peccato è esplicito:

```agda
sli      → gauge        -- ratio 30g          (Scalar)
budget   → bargauge     -- 1-(1-SLI)/(1-SLO)  (Scalar)
burnRate → stat         -- (1-SLI₁ₕ)/(1-SLO)  (Scalar)
sliTrend → timeseries   -- ratio sui 5m       (InstantVector)
```

Tre `Scalar`, **tre widget diversi scelti a mano**. Il punto:

> `Prometea.PromType` collassa "ratio bounded ∈[0,1]" e "magnitudo unbounded"
> nello stesso tipo `Scalar`. La struttura che distingue `gauge` da `stat` —
> i *bounds* — è stata buttata via a monte. Quando l'informazione discriminante
> non è nel tipo, la scelta **non può** emergere: deve essere stipulata. È lì
> che il regime 3 si infila.

semeion non aggiunge un mapping più furbo sopra `Scalar`. **Reintroduce nel
tipo la struttura che `Scalar` ha dimenticato**, così la scelta cade fuori
come corollario.

---

## Come funziona

### Tre stadi di emergenza — non uno

```
Signal  ──teorema──▶  Display  ──adapter──▶  PanelKind  ──▶  JSON
(natura)            (primitiva             (nome Grafana)   (Penelope)
                     geometrica)
```

`Display` è la primitiva **geometrica**, nominata da *cos'è*, non da come la
chiama Grafana. Il nome del pannello è l'epifenomeno di un epifenomeno.
**semeion è una radice: dipende solo da `standard-library`, non importa
Penelope** (resta a monte — l'apeiron dei segnali).

```agda
data Display : Set where
  arc        : Display   -- un valore dentro un intervallo noto   (→ gauge)
  bars       : Display   -- N valori comparabili su una scala      (→ bargauge)
  number     : Display   -- una magnitudo senza fondoscala         (→ stat)
  line       : Display   -- una traiettoria continua nel tempo     (→ timeseries)
  stateBands : Display   -- una traiettoria categoriale            (→ status-history)
  grid       : Display   -- una famiglia non comparabile           (→ table)
```

### Il bounded è una PROVA, non una config

Un valore bounded è un razionale `v` dentro un intervallo **noto** `[lo,hi]`,
con i due testimoni `lo ≤ v` e `v ≤ hi` **incorporati** — non un campo
`min/max` da indovinare. Non puoi marcare *bounded* qualcosa senza esibirli:

```agda
record Bounded : Set where
  field
    lo hi v : ℚ
    lo≤v    : lo ≤ v          -- l'appartenenza all'intervallo
    v≤hi    : v ≤ hi          --   è DIMOSTRATA, non dichiarata

data Codomain : Set where
  flow  : Codomain                    -- magnitudo SENZA fondoscala: rate, latenza-ms
  ratio : Bounded → Codomain          -- bounded [lo,hi], testimoni incorporati: SLI, sat.
  state : (n : ℕ) → Fin n → Codomain  -- categoriale: n stati
```

Il caso canonico [0,1] **emerge** da `n ≤ d` (regime 1): `inUnit n d` prova
`0 ≤ n/d ≤ 1` — è il vecchio `m≤m+n` dell'SLI, ora su ℚ. Conseguenza onesta di
ℚ: `0/0` non esiste, quindi una lettura ratio esige denominatore `≠ 0` (zero
osservazioni non sono un SLI). Una magnitudo unbounded (un rate, una latenza in
ms) non ha testimoni da esibire: per questo finisce in `flow`, non in `ratio`.
La distinzione che `Scalar` aveva perso è di nuovo nel tipo.

### L'onestà è nel tipo

```agda
data Faithful : Set where
  forced          : Display → Faithful        -- emerge: unico fedele
  underdetermined : List Display → Faithful    -- la struttura non forza: menu onesto
```

Il **codominio** di `displayAt` testimonia se la scelta è emersa. Niente
funzione parziale più teorema a lato: la disonestà sarebbe rappresentabile, e
non lo è.

### L'intento è l'unica stipulazione — il K locale

Sotto `--without-K` non si assume K globalmente; lo si invoca, marcato, solo
dove una prova lo richiede. Allo stesso modo l'**intento** (`now` / `overTime`
— la domanda dell'operatore) **non è un campo del segnale**: è la sola
stipulazione, pagata al sito d'uso. Pagato l'intento, la struttura forza il
resto.

```agda
displayAt : Intent → Signal → Faithful
```

| Intento | Codominio | Indice | ⇒ Display | Regime |
|---|---|---|---|---|
| `overTime` | continuo | qualsiasi | **line** | 1 — traiettoria continua ⇒ linea |
| `overTime` | categoriale | qualsiasi | **stateBands** | 1 — una linea fra FAIL e OK è una *menzogna* |
| `now` | `ratio` | `point` | **arc** | 1 — l'intervallo intrinseco *è* l'arco |
| `now` | `ratio` | `comparable` | **bars** | 1 — N comparabili su una scala *sono* barre |
| `now` | `flow` | `point` | **number** | 1 — niente fondoscala ⇒ un arco avrebbe estremi fiat |
| `now` | `flow` | `mixed` | **grid** | 1 — unità eterogenee ⇒ tabella |
| `now` | `flow` | `comparable` | **underdetermined** | **3 — gusto, marcato** |

L'unica cella di gusto residua (magnitudi unbounded comparabili, *adesso*:
lista di stat vs tabella) **non viene scelta di nascosto** — il tipo dice
`underdetermined`.

### Il segnale richiesto: ratio / SLI

Un SLI è `good/total`, `0 ≤ good ≤ total` ⇒ `Codomain = ratio`, e **questo è
regime 1, un teorema**: l'appartenenza a [0,1] emerge da cos'è un SLI.

```agda
sliNow  : ∀ r → displayAt now      (mkSignal (ratio r) point) ≡ forced arc
sliNow  _ = refl                              -- "scalare → gauge" NON è più un fiat

sliTrend : ∀ r → displayAt overTime (mkSignal (ratio r) point) ≡ forced line
sliTrend _ = refl                             -- = il `sliTrend → timeseries` di SLO.agda

sliFamily : ∀ r → displayAt now (mkSignal (ratio r) comparable) ≡ forced bars
sliFamily _ = refl                            -- per-servizio, tutti in [0,1] ⇒ barre
```

Le scelte che `SLO.agda` faceva a mano sono ora **teoremi** (`refl`). L'unico
fiat — *quale* intento — è nominato, non nascosto sotto "scalare → gauge".

E il payoff falsificabile, il **rifiuto onesto**:

```agda
latencyIsNumber : displayAt now (mkSignal flow point) ≡ forced number
latencyIsNumber = refl

latencyNotArc   : displayAt now (mkSignal flow point) ≢ forced arc
latencyNotArc ()              -- la latenza p99 è unbounded: semeion RIFIUTA la gauge
```

La p99 come gauge (fondoscala inventato) è un peccato comune in Grafana.
semeion lo rende un *errore di tipo*: appena rimetti i bounds nel tipo, le tre
`Scalar` di `SLO.agda` (`sli`/`budget`/`burn`) si separano da sole.

---

## La metafora

σημεῖον — il **segno**, e insieme il **punto**: la Definizione 1 degli
*Elementi*, *σημεῖόν ἐστιν, οὗ μέρος οὐθέν* — «un punto è ciò che non ha
parte». Da lì comincia la geometria. semeion dà ai segnali una geometria.

L'àugure non *sceglie* cosa significa il volo degli uccelli: lo **legge** —
il significato è forzato dal segno, non stipulato dall'interprete. È la
differenza fra regime 1 e regime 3.

| semeion            | semantica / visualizzazione                       |
|--------------------|---------------------------------------------------|
| il segno-punto     | `Signal` — la natura del segnale, non il `kind`    |
| leggere il segno   | `displayAt` — la forma forzata dalla struttura     |
| l'iride / l'arco   | `arc` — i bounds [0,1] *sono* il fondoscala        |
| la lancetta        | il valore forzato, non scelto                      |
| il campo dei segni | i segnali grezzi, prima che la forma emerga        |
| `forced d`         | il presagio univoco: emerge                        |
| `underdetermined`  | il segno muto: nessuna forma è forzata — dillo     |
| l'intento (K)      | la domanda dell'operatore — l'unico fiat onesto    |

> *Un segnale visualizzato a gusto è un presagio inventato.*

---

## Come libreria

```nix
# flake.nix del tuo progetto
inputs.semeion.url = "github:avit-io/semeion";
inputs.semeion.inputs.nixpkgs.follows = "nixpkgs";
inputs.semeion.inputs.piforge.follows = "piforge";

devShells.x86_64-linux.default =
  inputs.semeion.lib.mkShell {
    pkgs = nixpkgs.legacyPackages.x86_64-linux;
  };
```

```
# mio-progetto.agda-lib
name: mio-progetto
include: .
depend: standard-library semeion
```

### Come sviluppatore di semeion

```bash
git clone https://github.com/avit-io/semeion
cd semeion
nix develop                  # Agda 2.8 + stdlib (semeion è una radice)
agda Semeion/Signal.agda     # typecheck completo: 0 postulate, --safe --without-K
```

---

## Struttura del progetto

```
semeion/
├── Semeion/
│   ├── Signal.agda      # Signal (Codomain · Index) · Display · Faithful ·
│   │                    #   displayAt (il teorema) · le prove (SLI, rifiuto p99)
│   └── Vocab.agda       # vocabolario SRE: level/sli/rate/latency/burn ·
│                        #   saturation & error-budget come REGIME 2 (fedeltà)
├── semeion.agda-lib     # depend: standard-library (radice: zero dep d'ecosistema)
└── flake.nix            # packages.lib · lib.mkShell · devShells.default
```

---

## Relazione con l'ecosistema

Due ordini, da non confondere.

**Ordine concettuale** — cosa è prima *nel significato*. semeion è l'**ἄπειρον
dei segnali**: la natura indistinta (bounded? flow? categoriale? istante o
traiettoria?) da cui si separano le forme determinate. penelope, alla
convergenza, è **la tessitrice**.

```
            semeion  ← l'apeiron: la natura del segnale
               │  (da cui si separano le forme determinate)
   ┌───────────┼───────────┬───────────┐
   ▼           ▼           ▼            ▼
prometea     henql      loquel      agdovana
(valore)   (PromQL)   (log)       (allarmi)
   └───────────┴─────┬─────┴────────────┘
                     ▼
                 penelope  ← la tessitrice: lega Display ⊗ Expr ⊗ Pipe
```

**Ordine di dipendenza** — chi `import`-a chi. NON è un diamante a un apice:
prometea/henql/loquel sono valore e sintassi, non hanno bisogno della
geometria. La forma reale è una **foresta di radici** (solo `standard-library`:
`prometea`, `loquel`, **`semeion`**) che converge su penelope.

```
radici:   prometea     loquel     semeion        (depend: standard-library)
             │ └─henql    │           │
             ▼    ▼       ▼           │
           agdovana    penelope ◀─────┘
                       (depend: … prometea henql loquel semeion)
```

semeion non importa Penelope: espone `Display`, e l'adapter
`Display → PanelKind` — col ponte `Signal ↔ Expr` — vive in Penelope, la
tessitrice. Coerente con "JSON epifenomeno": semeion resta geometria pura.

---

## Garanzie strutturali

- **bounded non falsificabile** — `ratio` esige un `Bounded` con i testimoni
  `lo ≤ v ≤ hi`. Non puoi marcare bounded un rate: non hai i testimoni. La
  distinzione `gauge`/`stat` torna a poggiare su struttura, non su gusto.
- **emergenza dato l'intento** — pagato `now`/`overTime`, `displayAt` è
  `forced` su ogni cella tranne una. `sliNow`, `sliTrend`, `sliFamily`,
  `latencyIsNumber` sono `refl`.
- **rifiuto del fondoscala inventato** — `displayAt now (flow, point) ≢
  forced arc`: una magnitudo unbounded **non** è una gauge. Errore di tipo,
  non convenzione.
- **onestà nel tipo** — `Faithful` distingue `forced` da `underdetermined`.
  La cella di gusto (`now`, `flow`, `comparable`) ritorna `underdetermined`,
  non una scelta travestita.

`displayAt` è **totale**, `--safe --without-K`, **zero `postulate`**, zero
`TERMINATING`, zero `trustMe`.

### Cosa NON è garantito (onestà sopra tutto)

- **l'intento non emerge** — `now` vs `overTime` è la domanda dell'operatore,
  non una proprietà del segnale: lo stesso SLI è `arc` (now) *o* `line`
  (overTime), e `SLO.agda` mette giustamente *entrambi*. semeion non finge che
  un SLI "sia" una gauge — è il regime-2/3 nominato, l'unico K. Pagarlo una
  volta basta perché tutto il resto emerga.
- **una cella resta gusto** — `now` / `flow` / `comparable` (magnitudi
  unbounded comparabili): lista di stat vs tabella. Marcata
  `underdetermined`, non risolta di nascosto.
- **vocabolario solo [0,1]** — il *tipo* `Bounded` porta già `[lo,hi]`
  qualunque su ℚ, ma il vocabolario SRE (`Vocab`) ne usa solo l'unità [0,1]
  (SLI, saturazione, budget). Un segnale con cap noto fuori da [0,1] (es.
  temperatura, %>1) ha il tipo ma non ancora una voce: si aggiunge quando
  arriva, non a vuoto.
- **comparabilità è un enum, non una prova di unità** — `comparable` / `mixed`
  oggi sono dichiarati; la prova che due serie condividano davvero l'unità
  (un'algebra delle unità) è roadmap. Per i `ratio` la comparabilità è gratis
  ([0,1] è canonico); per i `flow` è ancora fede.

---

## Roadmap

In ordine di valore (regime fra parentesi):

1. **Generalizzazione del consumatore — `Determined A`** *(strutturale)* —
   `Faithful` è `Determined Display`: la dicotomia `forced | underdetermined`
   è epistemica (regime 1 vs 3), non specifica del rendering. Il segnale riduce
   la libertà di *ogni* consumatore a valle, non solo del widget. Estrarre
   `Determined (A : Set)` e derivarne `queryAt : Intent → Signal → Determined
   QueryShape` (PromQL / log) accanto a `displayAt`. La libertà residua resta
   esibita: `underdetermined xs` *è* lo spazio di scelta onesto, non l'assenza
   di vincolo.
2. **Testimoni distribuiti — il `Signal` porta più prove** *(fedeltà)* — la
   struttura si distribuisce in modo non uniforme tra i consumatori: il
   **bound** (`lo ≤ v ≤ hi`) forza il *widget* (`arc`), la **monotonicità** di
   un counter forza la *query* (`rate()` è la sola lettura fedele di un counter
   monotòno). Sono due testimoni diversi nello stesso segnale. Aggiungere
   `temporal : Temporal` al `Signal` (instant vs range vector; cumulativo vs
   gauge; staleness / regolarità del campionamento) così che `queryAt` lo
   consumi come `displayAt` consuma `cod`. Il payoff falsificabile è simmetrico
   al rifiuto della gauge sulla p99: `rate()` su un gauge diventa un **errore di
   tipo**, e un counter grezzo come `line` (senza `rate()`) è una menzogna che
   oggi semeion non sa rifiutare. Attenzione a non reintrodurre il regime 3 di
   nascosto — la window (`5m` vs `1m`) è gusto, il `now`/`overTime` del
   lato-query: va in `underdetermined`, non forzata.
3. **Algebra delle unità** *(da regime 3 a 1)* — il buco d'onestà più grave:
   `comparable` / `mixed` oggi sono enum dichiarati, non prove. Servono le
   dimensioni fisiche (tempo^a · byte^b · 1^c) con un'algebra che dimostri
   `unit s₁ ≡ unit s₂`, così che la comparabilità di due `flow` sia un
   **teorema**, non un tag. Senza, metà del giudizio `bars` vs `grid` poggia
   sul vuoto — il regime 3 travestito che semeion esiste per smascherare.
4. **Histogram / summary come codominio** *(regime 1)* — il leaf type più ricco
   di Prometheus manca del tutto: i bucket cumulativi `le` hanno una geometria
   forzata (`heatmap`, un nuovo `Display` additivo) e una regola di derivazione
   (i quantili). È l'assenza più grossa nel coprire «i segnali SRE».
5. **Algebra dei segnali** *(regime 1)* — `Signal → Signal → Signal` chiusa
   sotto le operazioni Prometheus (`sum`/`avg`/`histogram_quantile`/`topk`),
   con le regole di tipo: sommare due `ratio` **non** dà un `ratio` (esce da
   [0,1]); `histogram_quantile` su un istogramma dà un `flow`. Rende semeion un
   modello dei segnali *e delle loro trasformazioni*, non solo delle foglie.
6. **Aritmetica `ℚ` piena** *(abilitante)* — `Bounded` è già su ℚ; resta da
   spingere ℚ dove serve davvero (quantili, medie mobili, saturazione elastica)
   senza forzare tutto nello stampo conteggio-discreto.
7. **Adapter `Display → PanelKind`** *(lato Penelope)* — la mappa `arc↦Gauge`,
   `bars↦BarGauge`, `number↦Stat`, `line↦TimeSeries`, `stateBands↦StatusHistory`,
   `grid↦Table` (+ `heatmap↦Heatmap`), coi `FieldConfig`/`Viz` derivati come
   corollari (la soglia SLO dell'arco *è* un corollario di "target nel dominio
   bounded").

### Già implementato

- **Bounds generali `[lo,hi]` su ℚ** (`Bounded`) — oltre [0,1], col testimone
  `lo ≤ v ≤ hi` incorporato. Il caso unità emerge da `n ≤ d` (`inUnit`, regime
  1, il `m≤m+n` dell'SLI ora su ℚ); zero `postulate`.
- **Vocabolario SRE** (`Semeion/Vocab.agda`) — `level`, `rate`,
  `latencyQuantile`, `burnRate`, `sli` come osservabili con regime di
  boundedness incorporato. `saturation` ed `errorBudget` sono i casi
  **regime 2**: bounded solo sotto un'ipotesi falsificabile (`usage ≤
  capacity`, `bad ≤ budget`) fornita dall'operatore; senza, sono `flow` e la
  gauge è rifiutata. Il contrasto regime 1 (SLI, `m≤m+n`) vs regime 2
  (saturation) vive nel campo `Observable.regime`, dimostrato `refl`.

---

## Contribuire

Se trovi un segnale la cui forma è oggi stipulata e potrebbe **emergere**, o
una nostra "emergenza" che è in realtà gusto travestito, apri una issue:
*"semeion sta inventando un presagio"*.

---

## Licenza

MIT — il segno è libero, la lettura è forzata.

---

*semeion non interpreta. Legge. La forma di un segnale fedele non è una scelta
di chi guarda: è una proprietà di ciò che il segnale è.*

> *«Prima di scegliere come disegnare una metrica, chiediti che forma ha —*
> *e se la forma è davvero forzata, o la stai solo stipulando.»*
