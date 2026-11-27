# Predicting Primes · Part 3: editointimuistiinpanot

Muistiinpanot Part 3 -videon editoinnista, järjestyksessä sitä mukaa kuin niitä tulee.

## 1. Ruutu "How does the claimed proof get from the zeros to the exponent one half?"

**Nyt kuvassa:** vasemmalla laatikko, jossa keltainen pystyviiva ja sen päällä valkoiset nollat. Laatikossa ei ole akseleita, lukuja eikä funktion nimeä. Oikealla katkoviivaketju ympyröitä, joka päättyy merkintään x^(1/2).

**Korjattava:**
- Merkitse vaaka-akselille reaaliosan arvot **0**, **1/2** ja **1** (kriittinen kaista 0 < Re(s) < 1).
- Nimeä funktio: **ζ(s)** (zeta-funktio), jonka nollia pisteet ovat.
- Näytä, että kun reaaliosa on **1/2**, nollat asettuvat **keskipylvääseen** (kriittinen suora Re(s) = 1/2).

**Miksi:** ilman näitä merkintöjä kertojan puheen ja kuvan väliin jää aukko. Katsoja ei näe, että keltainen viiva on juuri Re(s) = 1/2, eikä siksi ymmärrä, mistä eksponentti 1/2 tulee.

**Ehdotus (ei vielä päätetty):** katkoviivaketjun alkuun tai päälle voisi lisätä välivaiheen Re(ρ) = 1/2 ⇒ |x^ρ| = x^(1/2). Silloin ketju kertoo, miten nollan reaaliosasta tulee eksponentti.

## 2. Ruutu "A first reading of the whole route"

**Nyt kuvassa:** yhdeksän palloa vaakaketjussa, vasemmassa reunassa teksti "the goal" ja alla "the route of the claimed proof, step by step". Seitsemän ensimmäistä palloa on keltaisia, kahdeksas on korostettu nykyiseksi kohdaksi ja yhdeksäs on tyhjä. Palloilla ei ole nimiä.

**Korjattava:**
- Kirjoita jokaisen pallon kohdalle, mikä todistuksen askel se on (lyhyt nimi pallon ylä- tai alapuolelle).
- Tyhjät pallot eivät kerro katsojalle mitään, vaikka otsikko lupaa lukea koko reitin.

**Avoinna:** askelten nimet ja niiden järjestys pitää vielä sopia. Niiden lähteeksi sopinee strategiakartta (`semantics/STRATEGY-argumenttikartta.html`, `verification/strategy/`).

## 3. Ruutu "What the reader's map is"

**Nyt kuvassa:** vasemmalla Lean-teksti piirrettynä harmaina palkkeina ("drawn as blocks in place of its words"). Oikealla kaavio: yläboksista lähtee nuolia kolmeen keskiboksiin ja niistä kahteen alaboksiin, ja osassa bokseja on vihreä ruksi. Yläpuolella teksti "CHECKED BY A SECOND AI MODEL · 37 rows of the list of claims, compared with the formal text".

**Korjattava:**
- Oikean puolen boksit ovat yhtä abstrakteja palkkeja kuin vasen Lean-teksti, joten kartta ei näytä eroavan tekstistä mitenkään. Bokseihin pitää kirjoittaa jotain hyödyllistä, esimerkiksi väitteen lyhyt nimi tai sisältö luonnollisella kielellä ja tarvittaessa viittaus vastaavaan Lean-lauseeseen.
- Silloin katsoja näkee, mitä lukijan kartta lisää: se kertoo sanoin, mitä vasemman puolen palkit väittävät ja miten väitteet riippuvat toisistaan.

**Huomioita samasta ruudusta (tarkistettava):**
- Luku 37 näyttää kuvakaappauksessa sotkuiselta ("ʒ7"). Se voi olla laskurianimaation välikuva, mutta tarkista lopullinen kuva.
- Vasemman keskiboksin päällä on ylimääräinen ääriviivakehys, joka ulottuu keskimmäiseen boksiin asti. Jos se on korostus, se näyttää nyt kohdistusvirheeltä.

## 4. Ruutu "Which statement uses which"

**Nyt kuvassa:** vasemmalla otsikko, selitteet (oranssi = "the files that it rests on", vihreä = "the files that are built on it") ja haalea teksti "the step that gives the exponent one half of the ceiling sits in this file" sekä x^(1/2). Oikealla tiedostojen pistekaavio (piste jokaista tiedostoa kohden), josta yksi piste on ympyröity ja nimetty "one file". Kaavio täyttää vain ruudun oikean reunan.

**Korjattava:**
- Taustan pistekaavion pitää täyttää ruudusta enemmän, ja sen pitää olla nykyistä himmeämpi, jotta vasemman puolen teksti erottuu.
- Kohtauksen loppuosassa nimen "one file" tilalle tulee hyödyllinen tieto, jos mahdollista: esimerkiksi tiedoston nimi tai polku ja lyhyesti se lause, joka antaa eksponentin 1/2.

**Avoinna:** mikä tiedosto on kyseessä. Nimi tarkistetaan repon `src`-hakemistosta ennen kuin se kirjoitetaan kuvaan.

## 5. Ruutu "The formal text in numbers"

**Nyt kuvassa:** vasemmalla kansioiden sisäkkäisistä renkaista koostuva pistekuva ("every file as a dot, inside the rings of its folders"). Oikealla luvut "about 149,000 files now" ja "about 15.0 million lines" sekä leima "AS OF 24 NOVEMBER 2026".

**Korjattava:**
- Vasemman puolen graafianimaatio on todennäköisesti turha, koska se pyörii ruudulla hyvin lyhyen aikaa. Se myös toistaa edellisen kohtauksen pistekaaviota.
- Sen tilalle tulee jotain hyödyllistä.

**Ehdotuksia korvaajaksi (ei vielä päätetty):**
- Tiedostot ja rivit jaettuna `src`-hakemiston pääkansioittain (esimerkiksi GroundTheory, PositivityTheory, ReciprocityTheory ja muut) yksinkertaisena pylväs- tai palkkikuvana.
- Kasvukäyrä, joka näyttää tiedostojen tai rivien määrän ajan mittaan 24.11.2026 asti.
