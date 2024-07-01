import re, os, sys, time, subprocess, threading, random


def print_and_run(cmd):
    print(' '.join(cmd), file=sys.stderr)
    subprocess.run(cmd, stdout=subprocess.PIPE, check=True)


def setting():
    global model, bound, simustep, nthreads, cutoff, toolbox, solver
    model, bound, simustep = '', 0, int(1e5)
    nthreads, cutoff = 8, 600
    toolbox, solver = '../build/bin', '../deps/kissat/build/kissat'

    args = sys.argv[1:]
    idx, n = 0, len(args)
    while idx < n:
        def check(arg):
            nonlocal idx
            idx += 1
            if idx >= n:
                print("*** 'btorsweeping' error: argument to '-{}' missing".format(arg))
                exit(1)

        def parse_int(arg):
            try:
                val = int(args[idx])
            except:
                print("*** 'btorsweeping' error: invalid number in '-{}'".format(arg))
                exit(1)
            return val

        if args[idx] == '--model':
            check('model')
            model = args[idx]
        elif args[idx] == '--bound':
            check('bound')
            bound = parse_int('bound')
        elif args[idx] == '--step':
            check('step')
            simustep = parse_int('step')
        elif args[idx] == '--nThreads':
            check('nThreads')
            nthreads = parse_int('nThreads')
        elif args[idx] == '--cutoff':
            check('cutoff')
            cutoff = parse_int('cutoff')
        elif args[idx] == '--toolbox':
            check('toolbox')
            toolbox = args[idx]
        elif args[idx] == '--solver':
            check('solver')
            solver = args[idx]
        else:
            print(
                "usage: python3 btorsweeping.py [ <option> ... ]\n"
                "\n"
                "where <option> is one of the following\n"
                "\n"
                "  --model <model>         load model from <model> in 'BTOR' format\n"
                "  --bound <b>             Bound to check up until <b> (default: 0)\n"
                "  --step <n>              generate <n> random transitions (default 100000)\n"
                "  --nThreads <t>          number of <t> threads allowed (default 8)\n"
                "  --cutoff <s>            the wall time for SAT solving is set to <s> (default 600 seconds)\n"
                "  --toolbox <path>        the path of the toolbox is set to <path> (default '../build/bin')\n"
                "  --solver <solver>       solving with the <solver> solver (default '../deps/kissat/build/kissat')\n"
            )
            exit(0)
        idx += 1

    global prefix, semaphore, fold
    name = os.path.basename(model)
    prefix = re.search(r'(\S+).btor2', name).group(1)
    semaphore = threading.Semaphore(value=nthreads)
    fold = '{}@{}'.format(name, hex(random.randint(0, (2 ** 64) - 1))[2:])
    toolbox, solver = os.path.abspath(toolbox), os.path.abspath(solver)

    print_and_run(['mkdir', '-p', fold])


def simulate():
    global out, enm
    enm = fold + '/{}.btor2'.format(prefix)
    gnm = fold + '/{}@eliminate.btor2'.format(prefix)
    out, log = fold + '/{}@res'.format(prefix), fold + '/{}@log'.format(prefix)

    s = random.randint(0, (2 ** 16) - 1)
    print_and_run(['{}/btorexpand'.format(toolbox), '--model', model, '--output', enm, '-e', str(bound)])
    print_and_run(['{}/btoreliminate'.format(toolbox), '--model', enm, '--output', gnm])
    print_and_run(
        ['{}/simubtor'.format(toolbox), '--model', gnm, '-s', str(s), '-r', str(simustep), '--log', log, '--output',
         out, '--check-all'])


def solve():
    tans, unsat_cnt, timeout_cnt, total = [], 0, 0, 0

    def run_cmd(x, y):
        nonlocal unsat_cnt, timeout_cnt, total, tans
        total += 1
        fnm = str(x) + '+' + str(y)
        onm = fold + '/{}@{}+{}'.format(prefix, x, y)
        try:
            cmd = ['{}/btorextract'.format(toolbox), '--model', enm, '--node', str(x), str(y), '0', '--output',
                   onm + '.btor2']
            res = subprocess.check_output(cmd, timeout=cutoff).decode()
            print('{} >> {}'.format(' '.join(cmd), res.strip()), file=sys.stderr)

            cmd = ['{}/btor2aiger'.format(toolbox), onm + '.btor2']
            print(' '.join(cmd), file=sys.stderr)
            with open(onm + '.aig', 'wb') as f:
                subprocess.run(cmd, stdout=f, universal_newlines=True, timeout=cutoff, check=True)

            cmd = ['{}/aiger2cnf'.format(toolbox), '--model', onm + '.aig', '--output', onm + '.cnf', '-pg']
            print(' '.join(cmd), file=sys.stderr)
            subprocess.run(cmd, timeout=cutoff, check=True)

            res = ''
            try:
                cmd = [solver, onm + '.cnf']
                print(' '.join(cmd), file=sys.stderr)
                temp = subprocess.check_output(cmd, timeout=cutoff)
            except subprocess.TimeoutExpired:
                timeout_cnt += 1
                print('--> timeout {}'.format(fnm), file=sys.stderr)
            except Exception as e:
                e = str(e)
                if e.count('exit status 20'):
                    unsat_cnt += 1
                    res = 'UNSATISFIABLE'
                    tans.append((x, y))
                elif e.count('exit status 10'):
                    res = 'SATISFIABLE'
                else:
                    exit(1)
                print('--> solve {} >> {}'.format(fnm, res), file=sys.stderr)
        except:
            print('--> error {}'.format(fnm), file=sys.stderr)
        semaphore.release()

    pool = []
    with open(out, 'r') as f:
        for pir in f.readlines():
            x, y = map(int, pir.split(' '))
            t = threading.Thread(target=run_cmd, args=(x, y,))
            t.daemon = True
            pool.append(t)

            semaphore.acquire()
            t.start()
    for t in pool:
        t.join()

    global listname
    listname = fold + '/{}@list'.format(prefix)
    with open(listname, 'w') as f:
        f.write('\n'.join('{} {}'.format(x, y) for x, y in tans))

    print('unsat: {}/{}'.format(unsat_cnt, total))
    print('timeout: {}/{}'.format(timeout_cnt, total))


def merge(listname):
    mergename = '{}@merge-bound{}'.format(prefix, bound)
    cmd = ['{}/btormerge'.format(toolbox), '--model', enm, '--list', listname, '--output', mergename + '.btor2']
    print(' '.join(cmd), file=sys.stderr)
    subprocess.run(cmd, stdout=subprocess.PIPE, timeout=cutoff, check=True)


setting()
try:
    simulate()
    solve()
    merge(listname)
except Exception as e:
    print(e)
    pass
print_and_run(['rm', '-rf', fold])
