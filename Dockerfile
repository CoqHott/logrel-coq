
## Init

# Use a base image with Coq 8.16
FROM coqorg/coq:8.16.1
RUN sudo apt-get update

## Setup shell

# Install Zsh
RUN sudo apt-get install -y zsh wget

# Download and apply the Grml Zsh configuration
RUN sudo wget -O /etc/zsh/zshrc https://git.grml.org/f/grml-etc-core/etc/zsh/zshrc
RUN sudo wget -O /etc/skel/.zshrc https://git.grml.org/f/grml-etc-core/etc/skel/.zshrc

# Set Zsh as the default shell for all existing users
RUN sudo sed -i 's|/bin/bash|/bin/zsh|g' /etc/passwd

# touch zshrc
RUN touch /home/coq/.zshrc

## Setup coq and project

# Install Equations and smpl
RUN opam install -y coq-equations.1.3+8.16 coq-smpl.8.16

# Copy files from your host to the container
COPY . /home/coq/formalization
RUN sudo chown -R coq:coq /home/coq/formalization

# Run make in the formalization directory
WORKDIR /home/coq/formalization
RUN make

## Setup ssh server

# Install openssh
RUN sudo apt-get install -y openssh-server

# Create the directory for the SSH daemon
RUN sudo mkdir /var/run/sshd

# Expose the SSH port
EXPOSE 22

## Finalize

# Setup password for ssh
RUN echo 'coq:coq' | sudo chpasswd

# Shell at container startup
CMD /bin/zsh
