# riemann-hypothesis

Projekti tehdään NeuroPaja-työtavalla. Lue ennen työtä repon `neuropaja` ohjeet `docs/periaatteet.md` ja `docs/tehtavat-ja-paatokset.md`.

## Tehtävät ja päätökset

Työjono on Draversalissa ja Markon päätökset Päätösjonossa.

| Asetus | Arvo |
| --- | --- |
| Päätösjonon projektiavain | `riemann-hypothesis` |
| Päätösjonon tunnisteiden etuliite | `rh-` |
| Draversalin puu | `riemann-hypothesis` (lapsikenttä `tasks`, otsikkokenttä `title`) |
| Päätösjonon avainlähde | repon juuren yksityinen `.env`, muuttuja `PAATOSJONO_TOKEN` |

`.env` on ohitettu tiedostossa `.git/info/exclude`, ja sen oikeudet ovat 0600.

## Kirjoitusasetukset

NeuroPajan kirjoitus- ja tarkastusskillit lukevat projektin tiedostojen sijainnit tästä taulukosta. Suhteelliset polut luetaan projektin juuresta.

| Asetus | Arvo |
| --- | --- |
| Semanttinen verkko | `semanttinen-verkko.json`, jonka kentät kuvaa skilli semanttinen-verkko |

Commitin portti tarkistaa semanttisen verkon jokaisessa commitissa, joka muuttaa verkotettua tekstiä tai sen verkkoa. Kun portti pysäyttää commitin, näytä löydökset käyttäjälle ja korjaa ne skillin semanttinen-verkko ohjeen mukaan, tai ohita ne käyttäjän vahvistuksella muuttujalla `SEMANTTINEN_VERKKO_OHITA=1`.
