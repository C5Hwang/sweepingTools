Build
-------------------------------------------------------------------------------

From the root directory configure and build as follows:

```shell
./setup-deps.sh   # install dependencies 
./configure.sh
cd build
make
```

All binaries are generated into directory `build/bin`

Usage
-------------------------------------------------------------------------------

Python script in 'scripts' calls binary to implement sweeping

### BTOR sweeping

```
usage: python3 btorsweeping.py [ <option> ... ]

where <option> is one of the following

  --model <model>         load model from <model> in 'BTOR' format
  --bound <b>             Bound to check up until <b> (default: 0)
  --step <n>              generate <n> random transitions (default 100000)
  --nThreads <t>          number of <t> threads allowed (default 8)
  --cutoff <s>            the wall time for SAT solving is set to <s> (default 600 seconds)
  --toolbox <path>        the path of the toolbox is set to <path> (default '../build/bin')
  --solver <solver>       solving with the <solver> solver (default '../deps/kissat/build/kissat')

```

### AIGER sweeping

```
usage: python3 aigersweeping.py [ <option> ... ]

where <option> is one of the following

  --model <model>         load model from <model> in 'AIG' format
  --step <n>              generate <n> random transitions (default 100000)
  --nThreads <t>          number of <t> threads allowed (default 8)
  --cutoff <s>            the wall time for SAT solving is set to <s> (default 600 seconds)
  --toolbox <path>        the path of the toolbox is set to <path> (default '../build/bin')
  --solver <solver>       solving with the <solver> solver (default '../deps/kissat/build/kissat')
```
