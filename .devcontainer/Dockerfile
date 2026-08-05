FROM mcr.microsoft.com/devcontainers/base:ubuntu

USER vscode
WORKDIR /home/vscode

# elan entra na IMAGEM, e não num comando de pós-criação: assim a criação do
# Codespace não gasta tempo instalando o Lean.
#
# `--default-toolchain none` de propósito — o `lean-toolchain` do projeto é que
# decide a versão, e o elan a busca sozinho no primeiro uso. Fixar uma versão
# aqui só baixaria uma que não vai ser usada.
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
