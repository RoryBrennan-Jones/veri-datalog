all: bin/datalog.dll

out/%.cs: datalog.g4
	antlr -o out/ -Dlanguage=CSharp -no-listener -visitor datalog.g4

def.cs: def.dfy
	dafny translate --unicode-char=false --include-runtime cs def.dfy

bin/datalog.dll: datalog/datalog.csproj out/datalogParser.cs def.cs datalog/AstBuilder.cs datalog/Program.cs
	dotnet build datalog/datalog.csproj --output bin

examples/trace.out: examples/trace.pl examples/connectivity2.pl
	swipl -l $< > $@

examples/%.trace: examples/trace.pl examples/%.pl
	swipl -l $< -g "consult('examples/$*.pl')" -g trace -g "go" -g notrace -g halt > $@

examples/%.thm: bin/datalog.dll examples/%.pl examples/%.trace
	dotnet $^ > $@

.PHONY: check
check: bin/datalog.dll examples/connectivity2.pl examples/trace.out
	dotnet $^

.PHONY: clean
clean:
	$(RM) -r out
	$(RM) examples/*.out
	$(RM) def.cs

.PHONY: printexamplenames
printexamplenames:
	for filename in examples/*.pl; do echo "$$filename"; done

.PHONY: thing
thing:
	for filename in examples/*.pl; do swipl -l examples/trace.pl -g "consult('$$filename')" -g trace -g "go" -g notrace -g halt; done

TESTS=$(wildcard examples/*.pl)
THMS=$(patsubst %.pl,%.thm,$(TESTS))

.PHONY: test
test: $(THMS)