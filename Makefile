.PHONY: opam build clean test

OPAM=opam
DUNE=dune
SWITCH=ptt
OCAML_VERSION=5.3.0

DEPS=dune dune-site menhir ocamlformat

CHAPTERS := 0_ulc 1_stlc 2_bt 3_poly \
		 	4a_unification 4b_hm \
			5a_extensions 5b_type_constructors

define CHAPTER_RULES
SRCS_$(1) := $$(shell find $(1) -name "*.ml" -o -name "dune" -o -name "dune-project")

build-$(1): $$(SRCS_$(1))
	@echo $(1)
	@cd $(1) && $(DUNE) build

test-$(1): build-$(1)
	@cd $(1) && $(DUNE) test

clean-$(1):
	@cd $(1) && $(DUNE) clean
endef

$(foreach ch,$(CHAPTERS),$(eval $(call CHAPTER_RULES,$(ch))))

build: $(foreach ch,$(CHAPTERS),build-$(ch))

test: $(foreach ch,$(CHAPTERS),test-$(ch))

clean: $(foreach ch,$(CHAPTERS),clean-$(ch))

opam:
	$(OPAM) init
	$(OPAM) switch create $(SWITCH) $(OCAML_VERSION)
	$(OPAM) install $(DEPS) -y
