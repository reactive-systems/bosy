FROM docker.io/ubuntu:focal AS toolbuilder

RUN apt-get update && DEBIAN_FRONTEND="noninteractive"  apt-get install -y  git bison build-essential clang cmake curl flex gcc git libantlr3c-dev libbdd-dev libboost-program-options-dev libicu-dev libreadline-dev mercurial psmisc unzip vim-common wget zlib1g-dev libsqlite3-dev python3-distutils rustc cargo python-is-python3 pip openjdk-8-jdk
RUN pip install toml
RUN curl -sSL https://get.haskellstack.org/ | sh
RUN git clone https://github.com/reactive-systems/bosy.git /root/bosy
RUN make tools -C /root/bosy
RUN make clean-source-tools -C /root/bosy


FROM docker.io/swift:5.4-focal


RUN dpkg --add-architecture i386
RUN apt-get update
RUN apt-get install -y libreadline-dev:i386 libsqlite3-dev
RUN git clone https://github.com/reactive-systems/bosy.git /root/bosy
RUN swift build --configuration release -Xcc -O3 -Xcc -DNDEBUG -Xswiftc -Ounchecked --package-path=/root/bosy
#copy everything
#COPY --from=toolbuilder /root/bosy/Tools/* /root/bosy/Tools/
# default tools
COPY --from=toolbuilder /root/bosy/Tools/abc /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/bloqqer /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/bloqqer-031 /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/cadet /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/cryptominisat5 /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/ltl2tgba /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/ltl3ba /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/idq /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/quabs /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/rareqs /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/syfco /root/bosy/Tools/
COPY --from=toolbuilder /root/bosy/Tools/z3 /root/bosy/Tools/
#extra tools
#COPY --from=toolbuilder /root/bosy/Tools/aigbmc /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/smvtoaig /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/caqe /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/combine-aiger /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/cvc4 /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/depqbf /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/eprover /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/picosat-solver /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/vampire /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/hqs-linux /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/hqspre-linux /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/ltl2smv /root/bosy/Tools/
#COPY --from=toolbuilder /root/bosy/Tools/NuSMV /root/bosy/Tools/
WORKDIR /root/bosy
ENTRYPOINT ["/root/bosy/.build/release/BoSy"]
