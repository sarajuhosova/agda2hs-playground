# Agda2HS Playground

This repository is a playground for [Agda](https://agda.readthedocs.io/en/v2.6.2.2/) and [Agda2HS](https://github.com/agda/agda2hs).

To compile an Agda file to Haskell, run the following:

```bash
agda2hs <pathToFile>/<fileName>.agda -o _haskell
```

This will save the file under `_haskell/<moduleName>.hs`. `_haskell` is a gitignored directory.
