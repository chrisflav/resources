import Lake

open System Lake DSL

/-!
# Build configuration

This was a `lakefile.toml` until libsodium arrived. The TOML format describes
libraries, executables and dependencies and nothing else: it has no spelling for
compiling a C file or for linking a system library, which is what
`Resources/Crypto/Sodium.lean` needs. So the same four targets are spelled in
Lean here, with the C shim and the link flags added.

The shape is the one `leansqlite` uses, and for the same reasons: a `target`
that compiles one `.c` file to one `.o`, an `extern_lib` that archives it, and
`precompileModules` on the library that binds it so that the module initializer
-- `sodium_init` -- can run in the interpreter while later modules are being
elaborated, and not only in a linked binary.

## Where libsodium comes from

`pkg-config libsodium` is asked once, while this file is elaborated, for the
include path and the link flags. On Debian and in a NixOS build that path is
whatever `pkg-config` says, which is the point: nothing here names a directory
under `/usr` or `/nix/store`.

A deployment therefore needs libsodium's development files and `pkg-config` on
the machine that *builds*, and the shared library on the machine that *runs*.
On NixOS that is `buildInputs = [ pkgs.libsodium ]` and
`nativeBuildInputs = [ pkgs.pkg-config ]`, which puts `libsodium.pc` on
`PKG_CONFIG_PATH`; the store path it prints is written into the binary's
`RPATH`, so the built executable finds the same library it was linked against
with no `LD_LIBRARY_PATH`. On Debian it is `libsodium-dev` to build and
`libsodium23` to run.

If `pkg-config` cannot be asked at all, the link falls back to a plain
`-lsodium` and no extra include path, which is what a distribution that installs
the header in `/usr/include` wants anyway. A build with no libsodium at all
fails at the link, loudly, rather than producing a binary that cannot sign.
-/

/--
What `pkg-config` says about libsodium, or `fallback` if it cannot be asked --
because it is not installed, or because it does not know this library.
-/
private def pkgConfig (flag : String) (fallback : Array String) : IO (Array String) := do
  let out ←
    try
      IO.Process.output { cmd := "pkg-config", args := #[flag, "libsodium"] }
    catch _ =>
      return fallback
  if out.exitCode != 0 then return fallback
  return ((out.stdout.split Char.isWhitespace).toArray.map (·.toString)).filter
    (!·.isEmpty)

/-- Where libsodium's headers are, as `pkg-config --cflags` gives them. -/
def sodiumCFlags : Array String := run_io pkgConfig "--cflags" #[]

/--
What to link libsodium with.

Not `pkg-config --libs` as it comes. That is `-lsodium`, with a `-L` in front of
it only when the directory is not one a linker would search anyway — and
`-L/usr/lib/x86_64-linux-gnu` in front of Lean's own link line is a broken build
rather than a working one: Lean ships its own glibc and links `-lc` after this,
so a system library directory earlier in the search path is the system's libc
against Lean's startup files, which do not match.

So the library is named by the path of the file instead. A path is not a search
directory: it adds this one library and moves nothing else.

`-rpath` is added when that directory is not a system one, which is how a NixOS
build finds at run time the exact `libsodium` it was built against, with no
`LD_LIBRARY_PATH` and nothing installed globally. For `/usr/lib/...` it is left
off, because the loader looks there regardless and an `RPATH` naming it would
take precedence for every *other* library the binary needs as well.

`--allow-shlib-undefined` is the third of these, and it is about Lean rather than
about libsodium. Lean links against a deliberately old glibc so that its
binaries run on old systems, while the distribution's `libsodium.so` was built
against the glibc that distribution ships — so it names symbols (`fstat` as of
glibc 2.33, for one) that the stub Lean links against does not have, and `lld`
refuses a shared library with undefined symbols by default. At run time the
binary loads the system's real glibc, which has them. This says so. Undefined
symbols in *this* project's own objects are still an error.

If none of this can be worked out — no `pkg-config`, or a `libdir` with no
library in it — the flags fall back to a plain `-lsodium` and the link says what
is missing.
-/
private def sodiumLibs : IO (Array String) := do
  let libdir := (← pkgConfig "--variable=libdir" #[])[0]?
  let some dir := libdir | return ← pkgConfig "--libs" #["-lsodium"]
  let file := System.FilePath.mk dir / "libsodium.so"
  unless ← file.pathExists do return ← pkgConfig "--libs" #["-lsodium"]
  let system := dir.startsWith "/usr/lib" || dir.startsWith "/lib"
  return #[file.toString, "-Wl,--allow-shlib-undefined"]
    ++ (if system then #[] else #["-Wl,-rpath," ++ dir])

/-- What to link libsodium with, as `pkg-config` describes it. -/
def sodiumLinkFlags : Array String := run_io sodiumLibs

package resources where
  version := v!"0.1.0"
  -- The package's `moreLinkArgs` reach every executable, every precompiled
  -- module's shared library and the shim's own, which is each of the three
  -- places a libsodium symbol has to resolve.
  moreLinkArgs := sodiumLinkFlags

require leansqlite from git "https://github.com/leanprover/leansqlite" @ "v4.33.0"

require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.33.0"

/-- The C half of the libsodium binding, compiled against whatever `pkg-config` found. -/
target sodium_shim.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "sodium_shim.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "sodium_shim.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ sodiumCFlags
  buildO oFile srcJob weakArgs (traceArgs := #["-fPIC"]) (extraDepTrace := getLeanTrace)

/--
The shim, archived so that Lake links it into the executables and into the
shared library of every precompiled module. libsodium itself is not archived in
here: it is linked by `moreLinkArgs`, so one shared library is shared by all of
them.
-/
extern_lib sodium_shim pkg := do
  let oJob ← sodium_shim.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "sodium_shim") #[oJob]

/--
The library.

`precompileModules` is what makes `initialize` in `Resources/Crypto/Sodium.lean`
work: without it the interpreter has no `resources_sodium_init` to call when a
later module imports that one, and elaborating the rest of the library fails on
an unknown symbol rather than at the link.
-/
lean_lib Resources where
  needs := #[sodium_shim]
  precompileModules := true

/-- The tests, which are their own library so that the binary below stays a root. -/
lean_lib Test where
  globs := #[`Test.+]

@[default_target]
lean_exe resources where
  root := `Main

@[test_driver]
lean_exe test where
  root := `Test.Main
