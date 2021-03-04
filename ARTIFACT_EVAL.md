Hello artifact reviewer!

Thank you for taking the time to review Scooter and Sidecar :)

Our artifact consists of:
  1. The source for scooter and sidecar (written in rust)
  2. A series of case studies ported from other projects located in the
     benchmarks directory
  3. A benchmark that measures the performance of scooter's runtime enforcement

## Setting up your environment

### Recommended: Docker
We provide a docker image that contains all the required build- and runtime dependencies.
If you have docker installed just run:

```
make docker-prompt
```

And you'll be dropped into a shell capable of running everything.

**Note:** the files are shared between the docker prompt and your local OS so
you can use your own editor to poke around and make any changes you might
want. This can cause strangeness if you compile a binary inside the docker
container but try to run it from your host.

### Optional: Native
Scooter and Sidecar have been developed and tested on Linux and MacOS. Windows is untested
and our Makefile won't work there.

The project is written in rust. The recommended installation of stable rust is through rustup.rs:
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

In addition to rust we require `z3` (for verification) `mongodb` (for testing the runtime).
We require z3 >= 8.4.7. If you're on Ubuntu 20.04 (fossa) or later you should be able to just run:
```
sudo apt install z3
```

For mongodb you can follow the instructions on mongodb's [install
instructions](https://docs.mongodb.com/manual/administration/install-on-linux/)

## Duplicating the results

Once your environment is set up you can verify our results by running the following commands:

1. Verifying Case Studies (Sec. 5.1 & Fig. 5)

```
make case-studies
```

**Note:** Our LoC reported the submitted draft included empty lines. This will be fixed in the camera-ready. We have fixed the summary script to report the new lower line counts, but we
also report the old number which should match the table value in the draft.

2. ORM Performance Overhead (Sec. 5.3)

```
make bench
```


These commands may require builds or rebuilds of the source. Those builds may take a while.


## Playing around
Beyond what we present in the paper, feel free to experiment. Be warned the
parser generator we use unfortunately produces... unhelpful error messages.

### Generating counterexamples
We've included a case-study that is purposefully broken. Sidecar will report
an unsafe migration.

```
make case-studies/admin_changes
```


### Playing with the ORM
`mongodb-enforcement/example-project` contains a project set up and ready to experiment with.

### Playing with Sidecar (the static checker)
You can add your own case studies to the case studies folder for example:
```
mkdir case-studies/goofin-around
```

And create an initial policy and migration:

```
cd case-studies/goofin-around
touch policy.txt
touch 0-my-migration.mig
```

Migrations will be executed in lexicographical order, so prepending them with a
number ensures they execute in the proper order.

And run them with:

```
make case-studies/goofin-around
```
