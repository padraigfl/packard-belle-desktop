import React from "react";
import cx from "classnames";

import "./_background.scss";
import { SettingsContext } from "../../contexts/settings";

const Background = props => (
  <SettingsContext.Consumer>
    {context =>
      context.bgImg ? (
        <div
          className={cx("Background", {
            "Background--tiled": context.bgStyle === "tile",
            "Background--contain": context.bgStyle === "contain",
            "Background--stretch": context.bgStyle === "stretch"
          })}
        >
          <div style={{ backgroundImage: `url(${context.bgImg})` }} />
        </div>
      ) : null
    }
  </SettingsContext.Consumer>
);
export default Background;
