# Data Sources

## Seat counts

### Germany: 21st Bundestag (2025)
- **Source:** Bundeswahlleiterin (Federal Returning Officer), final official results
- **URL:** https://bundeswahlleiterin.de/en/info/presse/mitteilungen/bundestagswahl-2025/29_25_endgueltiges-ergebnis.html
- **Total seats:** 630 (majority threshold: 316)
- **Election date:** 23 February 2025

### France: 17th Assemblée Nationale (2024)
- **Source:** Assemblée nationale / Touteleurope.eu (parliamentary group composition)
- **URL:** https://www.touteleurope.eu/vie-politique-des-etats-membres/elections-legislatives-2024-quelle-repartition-des-sieges-dans-la-future-assemblee-nationale/
- **Total seats:** 577 (majority threshold: 289)
- **Election dates:** 30 June / 7 July 2024
- **Note:** Seat counts reflect parliamentary group composition as of late 2024.
  Numbers evolve slightly over the legislature due to reaffiliations and by-elections.

## Ideological positions

### Chapel Hill Expert Survey (CHES) 2019
- **Citation:** Jolly, S., Bakker, R., Hooghe, L., Marks, G., Polk, J., Rovny, J.,
  Steenbergen, M., & Vachudova, M.A. (2022). Chapel Hill Expert Survey Trend File,
  1999-2019. *Electoral Studies*, 75, 102420.
- **Variable used:** `lrgen` — overall left-right position (0 = extreme left, 10 = extreme right)
- **Dataset URL:** https://www.chesdata.eu/2019-chapel-hill-expert-survey
- **Direct download:** https://www.chesdata.eu/s/CHES2019V3.csv

### Notes on aggregation
- **CDU/CSU:** Treated as a single parliamentary group (208 seats). CHES provides
  separate scores: CDU = 5.86, CSU = 7.19. We use the seat-weighted average:
  (5.86 × 164 + 7.19 × 44) / 208 = **6.14**.
- **NFP (bloc model):** Seat-weighted average of LFI (1.25), PS (3.00), Écologistes (2.50),
  GDR/PCF (1.13): (1.25×71 + 3.00×69 + 2.50×38 + 1.13×17) / 195 ≈ **2.10**.
- **Ensemble (bloc model):** CHES provides Renaissance/LREM (6.33) and MoDem (6.13).
  Horizons (founded 2021) has no CHES 2019 entry; we approximate it as ≈ 6.2
  (positioned between MoDem and Renaissance). Seat-weighted average:
  (6.33×92 + 6.13×36 + 6.20×34) / 162 ≈ **6.26**.
- **RN bloc:** RN (9.75) + UDR/Ciotti (split from LR, approximated at 8.5):
  (9.75×122 + 8.50×17) / 139 = **9.60**.
- **Others:** LIOT (22) + non-inscrits (10). LIOT is a diverse centrist/regional group.
  We assign an approximate position of 5.0 (centrist) as no single CHES entry applies.
  Non-inscrits (unaffiliated) are likewise approximated at 5.0 (centrist default).
- **LR:** Standalone at 7.88 (49 seats), using the CHES value directly.

All approximated values are stored directly in `france_2024.csv` with rationale
in the `ches_source` column, so the analysis notebook computes all aggregations
from the CSV without hardcoded values.

### CHES 2024
- A new CHES wave covering 2024 was published in 2025 (Bakker et al., Electoral Studies, 2025).
  It would provide more current positions for French parties post-2024 realignment.
  URL: https://www.chesdata.eu/ches-europe
  We use the 2019 wave for consistency with the German case and because the 2024
  survey was not yet available when this analysis was initiated.
