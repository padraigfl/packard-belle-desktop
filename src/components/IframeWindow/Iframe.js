import React from "react";

class PureIframe extends React.PureComponent {
  shouldComponentUpdate() {
    return false;
  }
  render() {
    return <iframe title={this.props.title} {...this.props} />;
  }
}

export default PureIframe;
