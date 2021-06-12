default:
	cargo build

build:
	cargo build

test: mongod-exists
	mkdir -p ./.db
	mongod --dbpath=./.db --quiet --logpath=./.db/hidden.log & echo $$! > ./.db/pid
	cargo test
	@if [ -e ./.db/pid ]; then \
		kill -TERM $$(cat ./.db/pid) || true; \
	fi

case-studies: case-studies/hails/gitstar case-studies/hails/lambdachair case-studies/hails/lbh case-studies/lifty-conference case-studies/ur-calendar case-studies/visit-day case-studies/bibifi-history

case-studies/%: build
	@rm -f scripts/policy*.txt
	@cd scripts && pwd && ./run_case_study.sh $*
	scripts/summarize.sh case-studies/$*
	@printf "Successfully validated case-study: $*\n\n"

benchmark:
	mkdir -p ./.db
	mongod --dbpath=./.db --quiet --logpath=./.db/hidden.log & echo $$! > ./.db/pid
	cargo run -p postfriend --bin postfriend-bench --release 2000
	@if [ -e ./.db/pid ]; then \
		kill -TERM $$(cat ./.db/pid) || true; \
	fi

mongod-exists: ; @which mongod > /dev/null

docker-prompt:
	docker run --rm -it --network=host -v `pwd`:/data --entrypoint=/bin/bash -w=/data scootersidecar/artifact_eval
