# Pinned LRAT checker source

`drat-trim.c`, `lrat-check.c`, and `LICENSE` are copied without modification from
[`marijnheule/drat-trim`](https://github.com/marijnheule/drat-trim) at commit
`2e5e29cb0019d5cfd547d4208dca1b3ec290349f` (tag `v05.22.2023`).

Upstream source hashes:

- `lrat-check.c`: `05b3c92f6734fdfc9ee5c72217c9935540c1255b58bc9bdc134b6b26f5b43c9f`
- `drat-trim.c`: `f7619bdc338bc8151b2f6bb87488052795c926b048d5040cf165742eb1ba9a26`
- `LICENSE`: `71ab2a9dc5a294ad8fba4ccb8c45aaa8a439596d314a2a046ac9b62266872a18`

The bundled C checker and the independent Python checker in
`src/check_lrat.py` both verify the committed local-equality certificate.
