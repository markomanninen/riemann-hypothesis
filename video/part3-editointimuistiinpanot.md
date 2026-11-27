# Predicting Primes · Part 3: editointimuistiinpanot

Muistiinpanot Part 3 -videon editoinnista, järjestyksessä sitä mukaa kuin niitä tulee.

## Yleiset periaatteet

- **Tyhjää ääntä voi lisätä.** Tietyissä kohdissa ääniraitaan saa lisätä hiljaisuutta, jos grafiikkaa tai tekstiä pitää näyttää enemmän tai pidempään. Lisäykset tehdään harkiten, ja jokainen tarkistetaan erikseen: rytmi ei saa katketa, ja kertojan lause ei saa jäädä kesken.
- **Hengähdystauoissa tausta häivytetään** (ks. kohta 7).
- **Uuden matematiikan erottaminen (koskee kaikkia perehdytysjaksoja).** Selvitä jaksoja tehdessä, mikä osa todistuksesta on uutta matematiikkaa. Toisin sanoen: mitkä todistukset ja ideat ovat ne tärkeimmät, jotka varsinaisesti ratkaisevat RH:n, ja mikä on tunnettua tekniikkaa tai kirjanpitoa. Jakson pitää kertoa katsojalle, missä uusi idea on.
  - Lähde repossa: `verification/novelty/` luokittelee todistuksen 64 askelta luokkiin K (julkaistu ennen), A (tunnettu tekniikka uudessa käytössä), N (lähdettä ei löytynyt), G (kirjanpitoa) ja U (ei vertailukelpoinen). Kirjallisuushaun tuloksia ei README:n mukaan ole vielä (tehtävä `rh-novelty-literature-search`). Tarkista tilanne ennen kuin jaksossa sanotaan mitään uutuudesta.
  - Ennen tuloksia uutuudesta puhutaan väitteenä, ei toteamuksena.

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

## 6. Viimeinen jakso: kaksi askelta ja kaksi tarviketta

**Nyt kuvassa:** "first step": jos katto pätee, kriittisen suoran oikealla puolella ei ole nollia. "second step": jos kaksi asiaa on annettu, katto pätee. Toiseen askeleen tulevat nuolet kahdesta katkoviivaboksista: "an auxiliary field with a property" ja "lattices with their conditions". Alhaalla vasemmalla tekstit "Station 2 tells where the field comes from" ja "Station 5 belongs to the part that proves the conditions".

**Arvio:** rakenne toimii. Ketju tarvikkeet → askel 2 → askel 1 on selvä, ja kaksi askelta ja kaksi tarviketta näkyvät samassa kuvassa. Kolme aiempaa lupausta jää kuitenkin osin lunastamatta:

- **Eksponentti 1/2 puuttuu.** Part 3 alkoi kysymyksellä, miten nollista päästään eksponenttiin 1/2 (kohta 1). Tässä ruudussa ei sanota, että katto on x^(1/2), eikä askeleen 1 ikonin suoraa ole merkitty Re(s) = 1/2:ksi. Ikonissa on sama akseliton laatikko kuin kohdassa 1.
- **Asemat 2 ja 5 eivät avaudu.** Reittiruudun asemia ei nimetty (kohta 2), joten katsoja ei tiedä, mitä "Station 2" ja "Station 5" ovat. Korjaus: näytä tässä reitin yhdeksän palloa pienenä ja väritä, mihin boksiin kukin asema kuuluu.
- **x^(1/2)-tiedosto ei kytkeydy tähän.** Kohdan 4 tiedosto ("the step that gives the exponent one half sits in this file") kannattaa merkitä siihen boksiin, johon se kuuluu.

**Pienempiä huomioita:**
- "No zero lies to the right of the line" voi jättää katsojalle kysymyksen vasemmasta puolesta. Puolilause nollien symmetriasta suoran Re(s) = 1/2 suhteen sulkisi aukon.
- Kerro lopussa jokaisen boksin tila: mikä on Leanilla tarkistettu ja mikä on vielä väitettä. Muuten "claimed proof" -kehys jää auki.

## 7. Hengähdystauot (yleinen sääntö), esimerkkinä "Station 1 · A statement about zeros"

**Nyt kuvassa:** taustalla kirkkaansininen tiedostokartta kansionimineen (Abelian Variety Theory, Weil Bound, Reciprocity Theory ...). Sen päällä kortti "Station 1 in the formal text · Landau Theorems", jossa polku Development › Automorphic Arithmetic › Dedekind L Functions ja selite: tiedosto Zero Free Of Rpow Window sisältää askeleen, joka vie ikkunoiden katosta nollia koskevaan väitteeseen. Ylhäällä oikealla kuuden aseman ikonirivi.

**Korjattava, koskee kaikkia vastaavia taukoja:**
- Taustan animaatio häivytetään hengähdystauoissa selvästi nykyistä enemmän, jotta otsikot ja kortin teksti erottuvat.

**Huomioita tästä ruudusta (tarkistettava):**
- Kansionimet leikkautuvat kortin reunaan ("…pondence", "…ndations", vasemmassa reunassa yksinäinen "A"). Himmeämpi tausta vähentää tätä; nimet voi myös piilottaa kortin alta kokonaan.
- Haalea "Development"-teksti on aivan otsikkorivin alla ja sekoittuu siihen.
- Ruutu lunastaa osan kohtien 2 ja 4 lupauksista: asemilla on ikonit, ja x^(1/2)-askeleen tiedosto nimetään (Zero Free Of Rpow Window). Tarkista, että sama nimi näytetään myös kohdan 4 ruudussa "one file" -merkinnän tilalla.

## 8. Ruutu "Station 3 · Primes in classes: Adding up over a subgroup"

**Nyt kuvassa:** vasemmalla luokat 1–4 (mod 5), joista aliryhmä {1, 4} on korostettu, ja niiden alla karakterit χ0–χ3. Oikealla teksti "a subgroup, the classes 1 and 4", kolme kertolaskuriviä (1·1 → 1, 1·4 → 4, 4·4 = 16 = 3·5 + 1 → 1) ja "combining two members gives a member again".

**Korjattava:**
- Loppuosan tekstit ovat näkyvillä liian vähän aikaa: rivit ilmestyvät yksi kerrallaan, ja kokonaisuus ehtii olla ruudulla vain hetken ennen siirtymää.
- Korjaus: tuo kolme kertolaskuriviä ja alateksti näkyviin nopeammin, yhdellä pyyhkäisyllä. Pidä sen jälkeen valmis kuva ruudulla, kunnes kertoja on lopettanut, ja vielä hetki sen päälle.
- Jos rivien tahti on sidottu kertojan puheeseen, vaihtoehto on pidentää valmiin kuvan loppupitoa, kunhan valmis kuva on ruudulla riittävän kauan.

## 9. Ruutu "Station 4 · One slope between two bounds: Eleven conditions on a list of real numbers"

**Nyt kuvassa:** vasemmalla yksitoista ehtoriviä muotoa "— < —", joista neljä on korostettu ja numeroitu 1–4 ("the four that this station tells"). Keskellä laatikko "taken as given", jossa on neljä riviä ("four further statements"). Oikealla nuoli palkkiin "a bound on that excess".

**Korjattava:**
- Korostetut ehdot ovat yhtä tyhjiä kuin reittiruudun pallot (kohta 2). Näytä vähintään asema 4:n omat neljä ehtoa sanoin tai kaavana, esimerkiksi lyhyt muoto rivin sisällä tai rivin vieressä.
- Kirjanpito ei täsmää ruudulla: 11 = 4 korostettua + 4 annettua + 3, joita ei mainita. Kerro, mihin kolme muuta ehtoa kuuluvat, tai näytä se.
- Tarvittaessa lisää tähän hiljaisuutta (ks. yleiset periaatteet), jotta ehtojen sisällön ehtii lukea.

**Avoinna:** tulevatko "taken as given" -ehdot ja kolme mainitsematonta ehtoa esille myöhemmin? Loppujakson ruudun (kohta 6) mukaan "Station 5 belongs to the part that proves the conditions", joten annetut ehdot ehkä todistetaan asemalla 5. Jos niin on, se kannattaa sanoa tässä ääneen tai merkitä näkyviin ("→ asema 5").

**Tarkistettava:**
- Alateksti "the four that this station tells" on kuvakaappauksessa rikkinäinen (glitch-efekti tai animaation välikuva).
- Numero 4 on himmeä, vaikka rivi on korostettu. Se on ehkä vielä ilmestymässä.

## 10. Taustamusiikki: toinen pätkä alussa

**Ongelma:** videon alussa soiva toinen musiikkipätkä on liian voimakas, ja kertojan puhetta on vaikea kuulla sen alta. Pätkän dynamiikka vaihtelee luultavasti enemmän kuin muiden pätkien.

**Korjausvaihtoehdot:**
- Siloittele dynamiikkaa kompressorilla, jotta voimakkaat kohdat eivät nouse puheen päälle.
- Laske pätkän äänenvoimakkuutta.
- Tai tee molemmat: ensin kompressio, sitten taso muiden pätkien kanssa samaan.
- Vaihtoehtoisesti musiikki voi väistää puhetta automaattisesti (ducking/sidechain kertojan raidasta).

**Tarkistettava:** kuuntele lopuksi koko alku putkeen, jotta siirtymä ensimmäisestä pätkästä toiseen ei hyppää äänenvoimakkuudessa.
