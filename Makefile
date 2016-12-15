build:
	cp pkg/META.in pkg/META
	ocaml pkg/build.ml native=true native-dynlink=true

test: build
	rm -rf _build/tests
	ocamlbuild -classic-display -use-ocamlfind tests/PpxHardcamlTest.byte --

clean:
	ocamlbuild -clean
	rm -f pkg/META
	rm -f ppx_hardcaml.install

.PHONY: build test clean

VERSION      := $$(opam query --version)
NAME_VERSION := $$(opam query --name-version)
ARCHIVE      := $$(opam query --archive)

release:
	git tag -a v$(VERSION) -m "Version $(VERSION)."
	git push origin v$(VERSION)
	opam publish prepare $(NAME_VERSION) $(ARCHIVE)
	cp -t $(NAME_VERSION) descr
	grep -Ev '^(name|version):' opam >$(NAME_VERSION)/opam
	opam publish submit $(NAME_VERSION)
	rm -rf $(NAME_VERSION)

.PHONY: release
