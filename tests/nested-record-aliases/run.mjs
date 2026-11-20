// Regression test for type-checking records built from nested extensible
// aliases.
//
// Programs often build one large record type from per-module parts:
//
//     type alias Translations =
//         Header.Translations (Cart.Translations (Page.Translations {}))
//
// where each part is `{ t | header : { … } }` and parts include each other
// (a page includes the components it uses, which the top level lists too).
// Type-checking such a type must not cost memory per path through the
// aliases, and mistakes involving it must keep giving the same messages.
//
// Usage: node tests/nested-record-aliases/run.mjs <path to elm binary> [--record]
//
// --record writes the expected messages from the given compiler. They were
// recorded with v0.19.3-dev0002, except
// overload-needed-at-a-record-from-another-module, recorded with this
// change.

import { spawnSync } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const expectedDir = path.join(here, "expected");

const elm = path.resolve(process.argv[2] ?? "whelm");
const record = process.argv.includes("--record");

// Today's v0.19.3-dev0002 needs about 735 MB of live heap for the generated
// program below, so it fails within this limit.
const heapLimit = "400m";

const elmJson = {
  type: "application",
  "source-directories": ["src"],
  "elm-version": "0.19.2",
  dependencies: {
    direct: { "elm/core": "1.0.2", "elm/json": "1.1.2" },
    indirect: {},
  },
  "test-dependencies": { direct: {}, indirect: {} },
};

const mainFooter = `

main : Program () () ()
main =
    Platform.worker
        { init = \\_ -> ( (), Cmd.none )
        , update = \\_ model -> ( model, Cmd.none )
        , subscriptions = \\_ -> Sub.none
        }
`;

// MEMORY: components, pages that include components, and a top level that
// includes every component and page.

const memoryProgram = ({ components, pages, perPage, annotations, fieldsPerComponent }) => {
  const files = {};
  for (let i = 0; i < components; i++) {
    const fields = Array.from({ length: fieldsPerComponent }, (_, j) => `f${j} : String`).join(", ");
    files[`C${i}.elm`] = `module C${i} exposing (T)\n\n\ntype alias T t =\n    { t | c${i} : { ${fields} } }\n`;
  }
  for (let i = 0; i < pages; i++) {
    const included = Array.from({ length: perPage }, (_, j) => (i * 7 + j * 3) % components);
    const imports = [...new Set(included)].sort((a, b) => a - b).map((x) => `import C${x}\n`).join("");
    const body = included.reduce((t, x) => `C${x}.T (${t})`, `{ t | p${i} : { heading : String } }`);
    files[`P${i}.elm`] = `module P${i} exposing (T)\n\n${imports}\n\ntype alias T t =\n    ${body}\n`;
  }
  const imports =
    Array.from({ length: components }, (_, i) => `import C${i}\n`).join("") +
    Array.from({ length: pages }, (_, i) => `import P${i}\n`).join("");
  let top = "{}";
  for (let i = 0; i < components; i++) top = `C${i}.T (${top})`;
  for (let i = 0; i < pages; i++) top = `P${i}.T (${top})`;
  const uses = Array.from(
    { length: annotations },
    (_, x) => `\n\nuse${x} : Model -> String\nuse${x} model =\n    model.flags.translations.c${x % components}.f0\n`,
  ).join("");
  files["Main.elm"] =
    `module Main exposing (main)\n\n${imports}\n\ntype alias Translations =\n    ${top}\n\n\n` +
    `type alias Model =\n    { flags : { translations : Translations } }\n${uses}${mainFooter}`;
  return files;
};

// Aliases with parameters nested in their own arguments, `Box (Box (… Int))`,
// and a chain of parameterless aliases over one, `T2 = Twice T1`: cheap when
// each argument is converted once, exponential in depth when it is copied
// into the fields as well. `g` is unannotated, so the type other modules read
// from Lib's interface is the inferred one.
const nestedParameterProgram = (depth) => {
  const nest = (alias) => {
    let t = "Int";
    for (let i = 0; i < depth; i++) t = `${alias} (${t})`;
    return t;
  };
  const chain = Array.from(
    { length: depth },
    (_, i) => `type alias T${i + 1} =\n    Twice ${i === 0 ? "Int" : `T${i}`}\n\n\n`,
  ).join("");
  return {
    "Lib.elm":
      `module Lib exposing (Box, T${depth}, Twice, g, twice, chained)\n\n\n` +
      `type alias Box a =\n    { value : a }\n\n\n` +
      `type alias Twice a =\n    { x : a, y : a }\n\n\n` +
      chain +
      `f : ${nest("Box")} -> Int\nf _ =\n    1\n\n\n` +
      `g =\n    f\n\n\n` +
      `twice : ${nest("Twice")} -> Int\ntwice _ =\n    1\n\n\n` +
      `chained : T${depth} -> Int\nchained _ =\n    1\n`,
    "Main.elm":
      `module Main exposing (main)\n\nimport Lib exposing (Box, T${depth}, Twice)\n\n\n` +
      `useG : ${nest("Box")} -> Int\nuseG =\n    Lib.g\n\n\n` +
      `useTwice : ${nest("Twice")} -> Int\nuseTwice =\n    Lib.twice\n\n\n` +
      `useChained : T${depth} -> Int\nuseChained =\n    Lib.chained\n${mainFooter}`,
  };
};

// MESSAGES: a small version of the same shape, with one mistake per case.

const supportModules = {
  "Head.elm": `module Head exposing (Translations)


type alias Translations t =
    { t | head : { defaultTitle : String, siteName : String } }
`,
  "Equipment.elm": `module Equipment exposing (Translations, title)

import Head


type alias Translations t =
    Head.Translations { t | equipment : { intro : String, count : Int } }


title : Translations t -> String
title t =
    t.head.defaultTitle ++ t.equipment.intro
`,
  "Page.elm": `module Page exposing (Translations)

import Equipment
import Head


type alias Translations t =
    Equipment.Translations (Head.Translations { t | page : { heading : String } })
`,
  "All.elm": `module All exposing (Model, Translations)

import Equipment
import Head
import Page


type alias Translations =
    Head.Translations (Equipment.Translations (Page.Translations {}))


type alias Model =
    { flags : { translations : Translations }, count : Int }
`,
  "Describe.elm": `module Describe exposing (Box(..))


type Box a
    = Box a


abstract describe : a -> String


Describe.describe : Box a -> String
Describe.describe _ =
    "box"


Describe.describe : List a -> String
    where Describe.describe : a -> String
Describe.describe xs =
    String.concat (List.map Describe.describe xs)
`,
  // Unannotated, so the types other modules see for these are the ones
  // inferred here, with All.Translations in them.
  "Value.elm": `module Value exposing (boxed, listed, translations)

import All
import Describe


empty : All.Translations
empty =
    { head = { defaultTitle = "", siteName = "" }
    , equipment = { intro = "", count = 0 }
    , page = { heading = "" }
    }


translations =
    empty


boxed =
    Describe.Box empty


listed =
    [ empty ]
`,
};

const cases = {
  "wrong-type": `import All exposing (Model)


heading : Model -> Int
heading model =
    model.flags.translations.page.heading
`,
  "missing-field": `import All exposing (Model)


heading : Model -> String
heading model =
    model.flags.translations.page.title
`,
  "literal-missing-field": `import All exposing (Translations)


empty : Translations
empty =
    { head = { defaultTitle = "", siteName = "" }
    , equipment = { intro = "", count = 0 }
    , page = {}
    }
`,
  "typo-in-part-field": `import All exposing (Model)


intro : Model -> String
intro model =
    model.flags.translations.equipment.intr
`,
  "unannotated-value-printed": `import All exposing (Model)


count : Model -> Int
count model =
    let
        translations =
            model.flags.translations
    in
    translations + 1
`,
  "parts-disagree-on-a-field": `import Head


type alias Other t =
    { t | head : { defaultTitle : Int, siteName : String } }


type alias Broken =
    Head.Translations (Other {})


title : Broken -> String
title t =
    t.head.siteName
`,
  "part-of-extensible-type": `import All exposing (Model)
import Equipment


intro : Model -> String
intro model =
    Equipment.title model.flags.translations
`,
  "overload-at-a-record-from-another-module": `import Describe
import Value


described : String
described =
    Describe.describe Value.translations
`,
  "overload-at-a-type-holding-a-record-from-another-module": `import Describe
import Value


described : String
described =
    Describe.describe Value.boxed
`,
  "overload-needed-at-a-record-from-another-module": `import Describe
import Value


described : String
described =
    Describe.describe Value.listed
`,
  // The cases below apply an alias to arguments, which is converted as
  // written; each also comes wrapped in an alias without parameters, which
  // goes through the flattening.
  "tag-row-extension-in-field-wrapped": `type tag Foo
type tag Bar


type alias W r =
    { tags : [ r | Foo ] }


type alias X =
    W [ Bar ]


x : X
x =
    { tags = Foo }


y : X
y =
    { tags = Bar }
`,
  "field-extension-bound-to-non-record-wrapped": `type alias W t =
    { inner : { t | a : Int } }


type alias X =
    W (Maybe Int)


f : X -> ()
f _ =
    ()
`,
  "argument-repeats-a-field-given-the-outer-type-wrapped": `type alias Inner t =
    { t | i : Int }


type alias Outer t =
    Inner { t | a : Int }


type alias X =
    Outer { a : String }


x : X
x =
    { i = 1, a = 1 }
`,
  "argument-repeats-a-field-given-the-argument-type-wrapped": `type alias Inner t =
    { t | i : Int }


type alias Outer t =
    Inner { t | a : Int }


type alias X =
    Outer { a : String }


x : X
x =
    { i = 1, a = "s" }
`,
  "field-extension-repeats-a-field-given-the-outer-type-wrapped": `type alias W t =
    { inner : { t | a : Int } }


type alias X =
    W { a : String }


x : X
x =
    { inner = { a = 1 } }
`,
  "field-extension-repeats-a-field-given-the-argument-type-wrapped": `type alias W t =
    { inner : { t | a : Int } }


type alias X =
    W { a : String }


x : X
x =
    { inner = { a = "s" } }
`,
  "tag-row-extension-in-field": `type tag Foo
type tag Bar


type alias W r =
    { tags : [ r | Foo ] }


x : W [ Bar ]
x =
    { tags = Foo }
`,
  "field-extension-bound-to-non-record": `type alias W t =
    { inner : { t | a : Int } }


f : W (Maybe Int) -> ()
f _ =
    ()
`,
  "argument-repeats-a-field-given-the-outer-type": `type alias Inner t =
    { t | i : Int }


type alias Outer t =
    Inner { t | a : Int }


x : Outer { a : String }
x =
    { i = 1, a = 1 }
`,
  "argument-repeats-a-field-given-the-argument-type": `type alias Inner t =
    { t | i : Int }


type alias Outer t =
    Inner { t | a : Int }


x : Outer { a : String }
x =
    { i = 1, a = "s" }
`,
  "field-extension-repeats-a-field-given-the-outer-type": `type alias W t =
    { inner : { t | a : Int } }


x : W { a : String }
x =
    { inner = { a = 1 } }
`,
  "field-extension-repeats-a-field-given-the-argument-type": `type alias W t =
    { inner : { t | a : Int } }


x : W { a : String }
x =
    { inner = { a = "s" } }
`,
};

// RUNNING

const writeProject = (dir, files) => {
  fs.mkdirSync(path.join(dir, "src"), { recursive: true });
  fs.writeFileSync(path.join(dir, "elm.json"), JSON.stringify(elmJson, null, 4));
  for (const [name, source] of Object.entries(files)) {
    fs.writeFileSync(path.join(dir, "src", name), source);
  }
};

const make = (dir, rtsArgs = []) => {
  const rts = rtsArgs.length > 0 ? ["+RTS", ...rtsArgs, "-RTS"] : [];
  const r = spawnSync(elm, ["make", "src/Main.elm", "--output=/dev/null", ...rts], {
    cwd: dir,
    encoding: "utf8",
  });
  if (r.error) {
    console.log(`could not run ${elm}: ${r.error.message}`);
    process.exit(2);
  }
  return { status: r.status, output: r.stdout + r.stderr };
};

// The report from its first `-- ` header on, without the progress output
// before it, or "(compiles)" when there is no error.
const report = ({ status, output }) => {
  if (status === 0) return "(compiles)\n";
  const start = output.search(/^-- /m);
  return start < 0 ? output : output.slice(start);
};

if (!fs.existsSync(elm)) {
  console.log(`no elm binary at ${elm}: run \`make\` in the repo root, or pass the binary as the first argument`);
  process.exit(2);
}

const root = fs.mkdtempSync(path.join(os.tmpdir(), "nested-record-aliases-"));
const results = [];

if (!record) {
  const dir = path.join(root, "memory");
  writeProject(
    dir,
    memoryProgram({ components: 40, pages: 40, perPage: 6, annotations: 50, fieldsPerComponent: 300 }),
  );
  const r = make(dir, ["-N1", "-A16m", `-M${heapLimit}`]);
  results.push({
    name: `type-checks within a ${heapLimit} heap`,
    ok: r.status === 0,
    why: r.output.slice(-400),
  });

  const nestedDir = path.join(root, "nested-parameters");
  writeProject(nestedDir, nestedParameterProgram(22));
  const n = make(nestedDir, ["-N1", "-A16m", `-M${heapLimit}`]);
  results.push({
    name: `aliases nested 22 deep through their parameters type-check within a ${heapLimit} heap`,
    ok: n.status === 0,
    why: n.output.slice(-400),
  });
}

fs.mkdirSync(expectedDir, { recursive: true });
for (const [name, body] of Object.entries(cases)) {
  const dir = path.join(root, name);
  writeProject(dir, { ...supportModules, "Main.elm": `module Main exposing (main)\n\n${body}${mainFooter}` });
  const actual = report(make(dir));
  const file = path.join(expectedDir, `${name}.txt`);
  if (record) {
    fs.writeFileSync(file, actual);
    console.log(`recorded ${file}`);
    continue;
  }
  const expected = fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "(no expected file)\n";
  results.push({
    name: `message: ${name}`,
    ok: actual === expected,
    why: `expected:\n${expected}\nactual:\n${actual}`,
  });
}

for (const r of results) {
  console.log(`${r.ok ? "PASS" : "FAIL"}  ${r.name}${r.ok ? "" : "\n      " + r.why.replace(/\n/g, "\n      ")}`);
}
const ok = results.every((r) => r.ok);
if (ok) {
  fs.rmSync(root, { recursive: true });
} else {
  console.log(`(generated programs kept in ${root})`);
}
process.exit(ok ? 0 : 1);
