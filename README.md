# Res-Blossom 🌺

![GitHub package.json version](https://img.shields.io/github/package-json/v/johnridesabike/re-blossom)
![npm peer dependency version](https://img.shields.io/npm/dependency-version/re-blossom/peer/bs-platform?label=ReScript)
![Node.js CI](https://github.com/johnridesabike/re-blossom/workflows/Node.js%20CI/badge.svg)
![GitHub](https://img.shields.io/github/license/johnridesabike/re-blossom)

Res-Blossom is a [ReScript](https://rescript-lang.org/) implementation of the
famous [blossom algorithm](https://en.wikipedia.org/wiki/Blossom_algorithm). It
finds a maximum matching of vertices on general, undirected, weighted graphs.

**[📖 Read the documentation](https://johnridesa.bike/re-blossom/)**

## Installation

You can add Res-Blossom to your project by running:
```sh
npm install res-blossom
```

You will need to edit your project's `bsconfig.json` file and list Res-Blossom in
the `bs-dependencies`.
```json
{
  "bs-dependencies": [
    "res-blossom"
  ]
}
```

## Development

Download the code:
```sh
git clone https://github.com/johnridesabike/re-blossom.git
```
If you want to make your own changes, then it's recommended to fork the
repository on GitHub and clone your forked version.

Install the dependencies:
```sh
npm install
```

Compile a production build:
```sh
npm run build
```

Run the ReScript watcher.
```sh
npm run start
```

Run the tests:
```sh
npm run test
```

Run benchmarks that compare it to the similar JavaScript algorithm:
```sh
npm run bench
```

Run benchmarks in a browser:
```sh
npm run browser
```
Then open the URL provided and navigate to the `__benchmarks__` directory.

To turn on debug logging, enable [rescript-logger](https://github.com/MinimaHQ/rescript-logger)
with the `RES_LOG` environmental variable:
```sh
RES_LOG=res-blossom=* npm run build
```

This code uses many terms and ideas from
["Efficient algorithms for finding maximum matching in graphs" by Zvi Galil, *ACM Computing Surveys*, 1986](https://doi.org/10.1145/6462.6502).
Reading the paper will make this code much more understandable.

