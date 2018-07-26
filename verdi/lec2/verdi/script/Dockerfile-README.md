Dockerfile documentation
========================

This directory contains Dockerfiles to create new Docker images for
running Verdi tests reproducibly.

The rest of this file explains how to build new Docker images.

Preliminaries
-------------

```bash
# Finish Docker setup if necessary.
sudo usermod -aG docker $(whoami)
# Then log out and back in.

# Obtain Docker credentials.
# (This is only necessary once per machine; credentials are cached.)
docker login
```

Create images
-------------

The following commands create the Docker images and upload
them to the [Docker Hub](https://hub.docker.com).
Be sure to first export the `$DOCKERID` variable
to the name of your Docker account.

```bash
# Create image in an empty directory, and upload to Docker Hub.
alias create_upload_docker_image=' \
  rm -rf dockerdir && \
  mkdir -p dockerdir && \
  (cd dockerdir && \
  cp -pf ../Dockerfile-$OS-$COQVER Dockerfile && \
  docker build -t $DOCKERID/$OS-for-$PROJECT-$COQVER . && \
  docker push $DOCKERID/$OS-for-$PROJECT-$COQVER) && \
  rm -rf dockerdir'

export OS=xenial
export COQVER=coq8.6
export PROJECT=verdi
create_upload_docker_image

export OS=xenial
export COQVER=coq8.6-32bit
export PROJECT=verdi
create_upload_docker_image

export OS=xenial
export COQVER=coq8.7
export PROJECT=verdi
create_upload_docker_image

export OS=xenial
export COQVER=coq8.7-32bit
export PROJECT=verdi
create_upload_docker_image

export OS=xenial
export COQVER=coq8.8
export PROJECT=verdi
create_upload_docker_image

export OS=xenial
export COQVER=coq8.8-32bit
export PROJECT=verdi
create_upload_docker_image
```

Cleanup
-------

After creating the Docker images, consider deleting the Docker containers,
which can take up a lot of disk space.

To stop and remove/delete all Docker containers:
```bash
docker stop $(docker ps -a -q)
docker rm $(docker ps -a -q)
```
or you can just remove some of them.
