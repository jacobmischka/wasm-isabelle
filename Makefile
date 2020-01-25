FLAGS=
NATIVE_WORD=Native_Word
WASM=WebAssembly

SESSIONS=-d ${WASM} -d ${NATIVE_WORD}

.PHONY: build

build: ${WASM} ${NATIVE_WORD}
	isabelle build ${SESSIONS} ${WASM}

jedit: ${WASM}/ROOT ${WASM} ${NATIVE_WORD}
	isabelle jedit ${SESSIONS} $<
