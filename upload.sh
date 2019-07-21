rm -rf /tmp/tools
mkdir /tmp/tools
stack install --local-bin-path=/tmp/tools
tar -zcvf /tmp/tools.tgz -C /tmp/tools .
gcloud auth login
gsutil cp /tmp/tools.tgz gs://tptp/
