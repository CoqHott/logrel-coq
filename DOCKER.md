
# Build Docker Image

A docker image can be built and generated via
```
docker build -t formalization .
docker save formalization > formalization-docker.tar
```

# Run Container

For running the container:
```
docker run -it formalization
```

This opens a shell in ~/formalization. The project has already been compiled by Docker.
To rebuild it:
```
make clean
make
```

# Access via SSH

The docker container is setup with a ssh server in case
the user wish to access the files remotely with their IDE.


To launch the ssh server and map port 22 to port 22 on the host:
```
docker run -d -p 22:22 formalization sudo /usr/sbin/sshd -D
```

And then to connect (username is 'coq' and password is 'coq' as well):
```
ssh coq@localhost
```
Note you might have to source .profile to get coq in the PATH
